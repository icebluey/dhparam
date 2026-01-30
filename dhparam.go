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
	P *big.Int // Prime
	G *big.Int // Generator
	Q *big.Int // Optional subprime (for DSA compatibility)
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

	for {
		// Generate a random prime q of (bits-1) bits
		q, err := rand.Prime(rand.Reader, bits-1)
		if err != nil {
			return nil, nil, err
		}

		// Calculate p = 2q + 1
		p := new(big.Int).Mul(q, big.NewInt(2))
		p.Add(p, big.NewInt(1))

		// Check if p is prime
		if p.ProbablyPrime(64) {
			if verbose {
				elapsed := time.Since(start)
				fmt.Fprintf(os.Stderr, "Generated safe prime after %d attempts in %v\n",
					counter+1, elapsed)
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
		count int
	}{}

	// Start worker goroutines
	for i := 0; i < threads; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()

			localCounter := 0
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

					// Check if p is prime
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
						localCounter = 0
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
		counter.Unlock()
		fmt.Fprintf(os.Stderr, "\nGenerated safe prime after ~%d attempts in %v using %d threads\n",
			totalAttempts, elapsed, threads)
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
		P *big.Int
		G *big.Int
	}

	_, err := asn1.Unmarshal(derBytes, &params)
	if err != nil {
		return nil, fmt.Errorf("failed to parse DH parameters: %w", err)
	}

	return &DHParams{
		P: params.P,
		G: params.G,
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
		P *big.Int
		G *big.Int
	}

	p := dhParams{
		P: params.P,
		G: params.G,
	}

	return asn1.Marshal(p)
}

func printDHParamsText(params *DHParams, w io.Writer) {
	fmt.Fprintf(w, "DH Parameters: (%d bit)\n", params.P.BitLen())
	fmt.Fprintf(w, "    prime:\n")
	printHexValue(w, params.P)
	fmt.Fprintf(w, "    generator: %d (0x%x)\n", params.G, params.G)

	if params.Q != nil {
		fmt.Fprintf(w, "    subprime:\n")
		printHexValue(w, params.Q)
	}
}

func printHexValue(w io.Writer, n *big.Int) {
	bytes := n.Bytes()
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

	// Check if P is a safe prime (P = 2Q + 1 where Q is also prime)
	q := new(big.Int).Sub(params.P, one)
	q.Div(q, big.NewInt(2))

	if !q.ProbablyPrime(64) {
		// Not a safe prime, but might still be valid
		fmt.Fprintf(os.Stderr, "Warning: P does not appear to be a safe prime\n")
	}

	// Check that G is a generator of the correct order
	// G^((P-1)/2) mod P should not equal 1
	exp := new(big.Int).Sub(params.P, one)
	exp.Div(exp, big.NewInt(2))
	result := new(big.Int).Exp(params.G, exp, params.P)

	if result.Cmp(one) == 0 {
		return fmt.Errorf("generator G is not of the correct order")
	}

	return nil
}
