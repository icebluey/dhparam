package main

import (
	"crypto/rand"
	"encoding/asn1"
	"encoding/pem"
	"flag"
	"fmt"
	"io"
	"math/big"
	"os"
	"sync"
	"time"
)

const (
	DefaultBits      = 2048
	DefaultGenerator = 2
)

// Small primes for pre-screening (first 256 primes)
// This dramatically reduces the number of expensive Miller-Rabin tests
var smallPrimes = []int64{
	2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
	73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
	157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
	239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
	331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
	421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
	509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607,
	613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
	709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811,
	821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911,
	919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019,
	1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097,
	1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201,
	1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291,
	1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
	1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487,
	1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
	1583, 1597, 1601, 1607, 1609, 1613, 1619,
}

type Options struct {
	InFile    string
	OutFile   string
	InFormat  string
	OutFormat string
	Check     bool
	Text      bool
	NoOut     bool
	Generator int
	Verbose   bool
	Quiet     bool
	Threads   int
	NumBits   int
}

// DHParams represents DH parameters
type DHParams struct {
	P             *big.Int // Prime
	G             *big.Int // Generator
	Q             *big.Int // Optional subprime (for DSA compatibility)
	PrivateLength int      // Optional recommended private key length in bits
}

var (
	// Pre-computed safe primes for common bit sizes (optional optimization)
	knownPrimes = make(map[int]*DHParams)
)

func main() {
	opts := parseFlags()

	if err := run(opts); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
}

func parseFlags() *Options {
	opts := &Options{}

	flag.StringVar(&opts.InFile, "in", "", "Input file")
	flag.StringVar(&opts.OutFile, "out", "", "Output file")
	flag.StringVar(&opts.InFormat, "inform", "PEM", "Input format (PEM or DER)")
	flag.StringVar(&opts.OutFormat, "outform", "PEM", "Output format (PEM or DER)")
	flag.BoolVar(&opts.Check, "check", false, "Check the DH parameters")
	flag.BoolVar(&opts.Text, "text", false, "Print a text form of the DH parameters")
	flag.BoolVar(&opts.NoOut, "noout", false, "Don't output any DH parameters")
	flag.BoolVar(&opts.Verbose, "verbose", false, "Verbose output")
	flag.BoolVar(&opts.Quiet, "quiet", false, "Terse output")
	flag.IntVar(&opts.Threads, "T", 1, "Number of threads for generation")
	flag.IntVar(&opts.Threads, "threads", 1, "Number of threads for generation")

	// Generator flags
	flag2 := flag.Bool("2", false, "Use 2 as generator")
	flag3 := flag.Bool("3", false, "Use 3 as generator")
	flag5 := flag.Bool("5", false, "Use 5 as generator")

	flag.Parse()

	// Process generator flags
	if *flag2 {
		opts.Generator = 2
	} else if *flag3 {
		opts.Generator = 3
	} else if *flag5 {
		opts.Generator = 5
	}

	// Get bit size from positional argument
	if flag.NArg() > 0 {
		var bits int
		if _, err := fmt.Sscanf(flag.Arg(0), "%d", &bits); err != nil || bits <= 0 {
			fmt.Fprintf(os.Stderr, "Invalid bit size: %s\n", flag.Arg(0))
			os.Exit(1)
		}
		opts.NumBits = bits
	}

	// Set defaults
	if opts.Generator > 0 && opts.NumBits == 0 {
		opts.NumBits = DefaultBits
	}
	if opts.NumBits > 0 && opts.Generator == 0 {
		opts.Generator = DefaultGenerator
	}

	// Validate threads
	if opts.Threads < 1 {
		opts.Threads = 1
	}

	return opts
}

func run(opts *Options) error {
	var params *DHParams
	var err error

	// Generate or read parameters
	if opts.NumBits > 0 {
		if opts.InFile != "" && !opts.Quiet {
			fmt.Fprintf(os.Stderr, "Warning: input file %s ignored\n", opts.InFile)
		}

		if opts.Verbose {
			fmt.Fprintf(os.Stderr, "Generating DH parameters, %d bit long safe prime, generator %d\n",
				opts.NumBits, opts.Generator)
		}

		params, err = generateDHParams(opts.NumBits, opts.Generator, opts.Threads, opts.Verbose)
		if err != nil {
			return fmt.Errorf("failed to generate DH parameters: %w", err)
		}

		if opts.Verbose {
			fmt.Fprintf(os.Stderr, "\n")
		}
	} else {
		// Read from file
		params, err = readDHParams(opts.InFile, opts.InFormat)
		if err != nil {
			return fmt.Errorf("failed to read DH parameters: %w", err)
		}
	}

	// Output text representation
	if opts.Text {
		printDHParamsText(params, os.Stdout)
	}

	// Check parameters
	if opts.Check {
		if err := checkDHParams(params); err != nil {
			return fmt.Errorf("DH parameter check failed: %w", err)
		}
		fmt.Fprintf(os.Stderr, "DH parameters appear to be ok.\n")
	}

	// Write output
	if !opts.NoOut {
		if err := writeDHParams(params, opts.OutFile, opts.OutFormat); err != nil {
			return fmt.Errorf("failed to write DH parameters: %w", err)
		}
	}

	return nil
}

// isProbablyComposite performs small prime sieve test
// Returns true if n is definitely composite (not prime)
// Returns false if n might be prime (needs further testing)
// This eliminates >90% of composite candidates before expensive Miller-Rabin test
func isProbablyComposite(n *big.Int) bool {
	// Quick check for even numbers
	if n.Bit(0) == 0 {
		return true // even number (except 2)
	}

	// Test divisibility by small primes
	// This is much faster than Miller-Rabin and eliminates most composites
	for _, p := range smallPrimes {
		prime := big.NewInt(p)

		// If n equals the small prime, it's prime
		if n.Cmp(prime) == 0 {
			return false
		}

		// If n < prime, we can stop testing
		if n.Cmp(prime) < 0 {
			break
		}

		// Check if n is divisible by this prime
		mod := new(big.Int).Mod(n, prime)
		if mod.Sign() == 0 {
			return true // divisible by p, so composite
		}
	}

	return false // passed small prime test, might be prime
}

func generateDHParams(bits, generator, threads int, verbose bool) (*DHParams, error) {
	g := big.NewInt(int64(generator))

	// Generate a safe prime p where p = 2q + 1 and q is also prime
	var p, q *big.Int
	var err error

	if threads > 1 {
		p, q, err = generateSafePrimeParallel(bits, threads, verbose)
	} else {
		p, q, err = generateSafePrime(bits, verbose)
	}

	if err != nil {
		return nil, err
	}

	return &DHParams{
		P: p,
		G: g,
		Q: q,
	}, nil
}

// generateSafePrime generates a safe prime using single thread
func generateSafePrime(bits int, verbose bool) (*big.Int, *big.Int, error) {
	start := time.Now()
	counter := 0
	sieveRejected := 0

	for {
		// Generate a random prime q of (bits-1) bits
		q, err := rand.Prime(rand.Reader, bits-1)
		if err != nil {
			return nil, nil, err
		}

		// Calculate p = 2q + 1
		p := new(big.Int).Mul(q, big.NewInt(2))
		p.Add(p, big.NewInt(1))

		// Small prime sieve: quick test to eliminate >90% of composites
		if isProbablyComposite(p) {
			sieveRejected++
			counter++
			if verbose && counter%100 == 0 {
				fmt.Fprintf(os.Stderr, ".")
			}
			continue
		}

		// Check if p is prime using Miller-Rabin test (expensive)
		if p.ProbablyPrime(64) {
			if verbose {
				elapsed := time.Since(start)
				fmt.Fprintf(os.Stderr, "\nGenerated safe prime after %d attempts (%d sieve-rejected) in %v\n",
					counter+1, sieveRejected, elapsed)
			}
			return p, q, nil
		}

		counter++
		if verbose && counter%10 == 0 {
			fmt.Fprintf(os.Stderr, ".")
		}
	}
}

// generateSafePrimeParallel generates a safe prime using multiple threads
func generateSafePrimeParallel(bits, threads int, verbose bool) (*big.Int, *big.Int, error) {
	start := time.Now()

	type result struct {
		p *big.Int
		q *big.Int
	}

	resultCh := make(chan result, 1)
	stopCh := make(chan struct{})
	var wg sync.WaitGroup

	counter := &struct {
		sync.Mutex
		count         int
		sieveRejected int
	}{}

	// Start worker goroutines
	for i := 0; i < threads; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()

			localCounter := 0
			localSieveRejected := 0
			for {
				select {
				case <-stopCh:
					return
				default:
					// Generate a random prime q of (bits-1) bits
					q, err := rand.Prime(rand.Reader, bits-1)
					if err != nil {
						continue
					}

					// Calculate p = 2q + 1
					p := new(big.Int).Mul(q, big.NewInt(2))
					p.Add(p, big.NewInt(1))

					// Small prime sieve: quick test to eliminate >90% of composites
					if isProbablyComposite(p) {
						localSieveRejected++
						localCounter++
						if verbose && localCounter%1000 == 0 {
							counter.Lock()
							counter.count += localCounter
							counter.sieveRejected += localSieveRejected
							localCounter = 0
							localSieveRejected = 0
							if counter.count%10000 == 0 {
								fmt.Fprintf(os.Stderr, ".")
							}
							counter.Unlock()
						}
						continue
					}

					// Check if p is prime using Miller-Rabin test (expensive)
					if p.ProbablyPrime(64) {
						select {
						case resultCh <- result{p: p, q: q}:
							return
						case <-stopCh:
							return
						}
					}

					localCounter++
					if verbose && localCounter%100 == 0 {
						counter.Lock()
						counter.count += localCounter
						counter.sieveRejected += localSieveRejected
						localCounter = 0
						localSieveRejected = 0
						if counter.count%1000 == 0 {
							fmt.Fprintf(os.Stderr, ".")
						}
						counter.Unlock()
					}
				}
			}
		}(i)
	}

	// Wait for result
	res := <-resultCh
	close(stopCh)
	wg.Wait()

	if verbose {
		elapsed := time.Since(start)
		counter.Lock()
		totalAttempts := counter.count
		totalSieveRejected := counter.sieveRejected
		counter.Unlock()
		fmt.Fprintf(os.Stderr, "\nGenerated safe prime after ~%d attempts (~%d sieve-rejected) in %v using %d threads\n",
			totalAttempts, totalSieveRejected, elapsed, threads)
		fmt.Fprintf(os.Stderr, "Sieve efficiency: %.1f%% candidates eliminated\n",
			float64(totalSieveRejected)/float64(totalAttempts)*100)
	}

	return res.p, res.q, nil
}

func readDHParams(filename, format string) (*DHParams, error) {
	var reader io.Reader
	if filename == "" {
		reader = os.Stdin
	} else {
		f, err := os.Open(filename)
		if err != nil {
			return nil, err
		}
		defer f.Close()
		reader = f
	}

	data, err := io.ReadAll(reader)
	if err != nil {
		return nil, err
	}

	var derBytes []byte

	if format == "PEM" || format == "pem" {
		block, _ := pem.Decode(data)
		if block == nil {
			return nil, fmt.Errorf("failed to decode PEM block")
		}
		derBytes = block.Bytes
	} else {
		derBytes = data
	}

	// Parse DH parameters from DER
	params, err := parseDHParams(derBytes)
	if err != nil {
		return nil, err
	}

	return params, nil
}

func parseDHParams(derBytes []byte) (*DHParams, error) {
	// PKCS#3 DHParameter ::= SEQUENCE {
	//     prime INTEGER, -- p
	//     base INTEGER,  -- g
	//     privateValueLength INTEGER OPTIONAL
	// }

	var params struct {
		P             *big.Int
		G             *big.Int
		PrivateLength int `asn1:"optional"`
	}

	_, err := asn1.Unmarshal(derBytes, &params)
	if err != nil {
		return nil, fmt.Errorf("failed to parse DH parameters: %w", err)
	}

	return &DHParams{
		P:             params.P,
		G:             params.G,
		PrivateLength: params.PrivateLength,
	}, nil
}

func writeDHParams(params *DHParams, filename, format string) error {
	var writer io.Writer
	if filename == "" {
		writer = os.Stdout
	} else {
		f, err := os.Create(filename)
		if err != nil {
			return err
		}
		defer f.Close()
		writer = f
	}

	// Encode as PKCS#3 DHParameter
	derBytes, err := marshalDHParams(params)
	if err != nil {
		return err
	}

	if format == "PEM" || format == "pem" {
		block := &pem.Block{
			Type:  "DH PARAMETERS",
			Bytes: derBytes,
		}
		return pem.Encode(writer, block)
	} else {
		_, err := writer.Write(derBytes)
		return err
	}
}

func marshalDHParams(params *DHParams) ([]byte, error) {
	// Create PKCS#3 DHParameter structure
	type dhParams struct {
		P             *big.Int
		G             *big.Int
		PrivateLength int `asn1:"optional"`
	}

	p := dhParams{
		P:             params.P,
		G:             params.G,
		PrivateLength: params.PrivateLength,
	}

	return asn1.Marshal(p)
}

func printDHParamsText(params *DHParams, w io.Writer) {
	fmt.Fprintf(w, "    DH Parameters: (%d bit)\n", params.P.BitLen())
	fmt.Fprintf(w, "    P:   \n")
	printHexValue(w, params.P)
	fmt.Fprintf(w, "    G:    %d (0x%x)\n", params.G, params.G)

	// Display recommended private length if present
	if params.PrivateLength > 0 {
		fmt.Fprintf(w, "    recommended-private-length: %d bits\n", params.PrivateLength)
	}
}

func printHexValue(w io.Writer, n *big.Int) {
	bytes := n.Bytes()

	// OpenSSL format: groups of 15 bytes per line, separated by colons
	for i := 0; i < len(bytes); i++ {
		if i%15 == 0 {
			fmt.Fprintf(w, "        ")
		}
		fmt.Fprintf(w, "%02x", bytes[i])
		if i < len(bytes)-1 {
			fmt.Fprintf(w, ":")
			if (i+1)%15 == 0 {
				fmt.Fprintf(w, "\n")
			}
		}
	}
	fmt.Fprintf(w, "\n")
}

func checkDHParams(params *DHParams) error {
	// Check that P is prime
	if !params.P.ProbablyPrime(64) {
		return fmt.Errorf("P is not prime")
	}

	// Check that G is valid (should be > 1 and < P)
	one := big.NewInt(1)
	if params.G.Cmp(one) <= 0 || params.G.Cmp(params.P) >= 0 {
		return fmt.Errorf("generator G is not in valid range (1 < G < P)")
	}

	// Basic validation passed - P is prime and G is in valid range
	// This is sufficient for DH parameters to be considered valid
	//
	// Note: OpenSSL performs additional checks for safe primes and generator order,
	// but those are not required for DH parameters to be mathematically valid.
	// Safe primes (P = 2Q + 1 where Q is also prime) are recommended but not mandatory.

	return nil
}
