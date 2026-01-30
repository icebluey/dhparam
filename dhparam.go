package main

import (
	"context"
	"crypto/rand"
	"encoding/asn1"
	"encoding/pem"
	"flag"
	"fmt"
	"io"
	"math/big"
	"os"
	"sync"
	"sync/atomic"
	"time"
)

const (
	DefaultBits      = 2048
	DefaultGenerator = 2
)

// ProgressCallback is called during prime generation to report progress
type ProgressCallback func(attempts int, sieveRejected int)

// isSafePrime checks if p is a safe prime (p = 2q + 1 where both p and q are prime)
// 
// Primality Testing Implementation:
// Go's math/big.Int.ProbablyPrime(n) uses:
// 1. Miller-Rabin test with n rounds
// 2. For n >= 1, it's effectively a Baillie-PSW equivalent test:
//    - First uses Miller-Rabin with base 2
//    - Then uses additional pseudoprime tests
// 3. With n=20: error probability < 2^(-40) = 10^(-12)
// 4. With n=64: error probability < 2^(-128) = 10^(-38) (cryptographic strength)
//
// Reference: https://golang.org/src/math/big/prime.go
//
// Note: q is already verified as prime by rand.Prime(), so we only test p
func isSafePrime(p *big.Int, qAlreadyPrime bool) (q *big.Int, isSafe bool) {
	one := big.NewInt(1)
	two := big.NewInt(2)
	
	// Calculate q = (p - 1) / 2
	q = new(big.Int).Sub(p, one)
	q.Div(q, two)
	
	// Use different iteration counts based on context
	// For p (the actual safe prime we're generating): use high iterations for security
	// For q (already from rand.Prime): fewer iterations if we need to double-check
	const pIterations = 64 // For p: cryptographic strength
	const qIterations = 20 // For q: sufficient when double-checking rand.Prime output
	
	// If q was already verified by rand.Prime(), skip its test
	if !qAlreadyPrime {
		if !q.ProbablyPrime(qIterations) {
			return nil, false
		}
	}
	
	// Check if p is prime (this is the expensive test we must always do)
	if !p.ProbablyPrime(pIterations) {
		return nil, false
	}
	
	// Both p and q are prime, so p is a safe prime
	return q, true
}

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

// Pre-computed big.Int versions of small primes to avoid repeated allocations
var smallPrimesBig map[int64]*big.Int

func init() {
	// Pre-compute big.Int versions of small primes
	smallPrimesBig = make(map[int64]*big.Int, len(smallPrimes))
	for _, p := range smallPrimes {
		smallPrimesBig[p] = big.NewInt(p)
	}
}

type Options struct {
	InFile     string
	OutFile    string
	InFormat   string
	OutFormat  string
	Check      bool
	Text       bool
	NoOut      bool
	Generator  int
	Verbose    bool
	Quiet      bool
	Threads    int
	NumBits    int
}

// DHParams represents DH parameters
type DHParams struct {
	P              *big.Int // Prime
	G              *big.Int // Generator
	Q              *big.Int // Optional subprime (for DSA compatibility)
	PrivateLength  int      // Optional recommended private key length in bits
}

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
	
	// Limit threads to reasonable maximum to avoid excessive goroutine creation
	// Generally, more threads than 4x CPU cores shows diminishing returns
	maxThreads := 256 // Absolute maximum
	if opts.Threads > maxThreads {
		fmt.Fprintf(os.Stderr, "Warning: limiting threads from %d to %d\n", opts.Threads, maxThreads)
		opts.Threads = maxThreads
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
	// Handle special cases
	if n.Sign() <= 0 {
		return true // negative or zero
	}
	
	two := big.NewInt(2)
	if n.Cmp(two) == 0 {
		return false // 2 is prime
	}
	
	// Quick check for even numbers
	if n.Bit(0) == 0 {
		return true // even number (not 2)
	}

	// Test divisibility by small primes
	// This is much faster than Miller-Rabin and eliminates most composites
	for _, p := range smallPrimes {
		prime := smallPrimesBig[p]
		
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

// GenerateWithContext generates DH parameters with context support and progress callback
// This is the public API for programmatic use with timeout and cancellation support
func GenerateWithContext(ctx context.Context, bits, generator, threads int, callback ProgressCallback) (*DHParams, error) {
	g := big.NewInt(int64(generator))

	// Generate a safe prime p where p = 2q + 1 and q is also prime
	var p, q *big.Int
	var err error

	if threads > 1 {
		p, q, err = generateSafePrimeParallelWithContext(ctx, bits, threads, callback, false)
	} else {
		p, q, err = generateSafePrimeWithContext(ctx, bits, callback, false)
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

func generateDHParams(bits, generator, threads int, verbose bool) (*DHParams, error) {
	g := big.NewInt(int64(generator))

	// Create context with timeout for very long generations
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Progress callback
	var callback ProgressCallback
	if verbose {
		callback = func(attempts, sieveRejected int) {
			if attempts%100 == 0 {
				fmt.Fprintf(os.Stderr, ".")
			}
		}
	}

	// Generate a safe prime p where p = 2q + 1 and q is also prime
	var p, q *big.Int
	var err error

	if threads > 1 {
		p, q, err = generateSafePrimeParallelWithContext(ctx, bits, threads, callback, verbose)
	} else {
		p, q, err = generateSafePrimeWithContext(ctx, bits, callback, verbose)
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

// generateSafePrimeWithContext generates a safe prime using single thread with context support
func generateSafePrimeWithContext(ctx context.Context, bits int, callback ProgressCallback, verbose bool) (*big.Int, *big.Int, error) {
	start := time.Now()
	attempts := 0
	sieveRejected := 0

	for {
		// Check context cancellation
		select {
		case <-ctx.Done():
			return nil, nil, ctx.Err()
		default:
		}

		// Generate a random prime q of (bits-1) bits
		q, err := rand.Prime(rand.Reader, bits-1)
		if err != nil {
			return nil, nil, err
		}

		// Calculate p = 2q + 1
		p := new(big.Int).Mul(q, big.NewInt(2))
		p.Add(p, big.NewInt(1))

		attempts++

		// Small prime sieve: quick test to eliminate >90% of composites
		if isProbablyComposite(p) {
			sieveRejected++
			if callback != nil && attempts%1000 == 0 {
				callback(attempts, sieveRejected)
			}
			if verbose && attempts%1000 == 0 {
				fmt.Fprintf(os.Stderr, ".")
			}
			continue
		}

		// Check if p is a safe prime (both p and q are prime)
		// q is already verified by rand.Prime(), so we only need to test p
		qVerified, isSafe := isSafePrime(p, true)
		if isSafe {
			if verbose {
				elapsed := time.Since(start)
				fmt.Fprintf(os.Stderr, "\nGenerated safe prime after %d attempts (%d sieve-rejected) in %v\n",
					attempts, sieveRejected, elapsed)
				fmt.Fprintf(os.Stderr, "Sieve efficiency: %.1f%% candidates eliminated\n",
					float64(sieveRejected)/float64(attempts)*100)
			}
			return p, qVerified, nil
		}

		if callback != nil && attempts%100 == 0 {
			callback(attempts, sieveRejected)
		}
		if verbose && attempts%100 == 0 {
			fmt.Fprintf(os.Stderr, ".")
		}
	}
}

// generateSafePrimeParallelWithContext generates a safe prime using multiple threads with First-Past-The-Post model
func generateSafePrimeParallelWithContext(ctx context.Context, bits, threads int, callback ProgressCallback, verbose bool) (*big.Int, *big.Int, error) {
	start := time.Now()

	// Result structure
	type result struct {
		p *big.Int
		q *big.Int
	}

	// Use buffered channel with capacity 1 for First-Past-The-Post
	resultCh := make(chan result, 1)
	
	// Create cancellable context for workers
	workerCtx, cancelWorkers := context.WithCancel(ctx)
	defer cancelWorkers()

	var wg sync.WaitGroup

	// Precise counters using atomic operations
	var totalAttempts atomic.Int64
	var totalSieveRejected atomic.Int64

	// Progress reporting goroutine (centralized output to avoid混乱)
	progressDone := make(chan struct{})
	if verbose || callback != nil {
		go func() {
			ticker := time.NewTicker(2 * time.Second)
			defer ticker.Stop()
			lastAttempts := int64(0)
			
			for {
				select {
				case <-ticker.C:
					attempts := totalAttempts.Load()
					sieveRej := totalSieveRejected.Load()
					
					if verbose && attempts > lastAttempts {
						fmt.Fprintf(os.Stderr, ".")
					}
					
					if callback != nil {
						callback(int(attempts), int(sieveRej))
					}
					
					lastAttempts = attempts
					
				case <-progressDone:
					return
				}
			}
		}()
	}

	// Start worker goroutines
	for i := 0; i < threads; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()

			for {
				// Check context cancellation FIRST (critical for resource cleanup)
				select {
				case <-workerCtx.Done():
					return
				default:
				}

				// Generate a random prime q of (bits-1) bits
				q, err := rand.Prime(rand.Reader, bits-1)
				if err != nil {
					continue
				}

				// Calculate p = 2q + 1
				p := new(big.Int).Mul(q, big.NewInt(2))
				p.Add(p, big.NewInt(1))

				// Atomic increment for precise counting
				totalAttempts.Add(1)

				// Small prime sieve: quick test to eliminate >90% of composites
				if isProbablyComposite(p) {
					totalSieveRejected.Add(1)
					continue
				}

				// Check if p is a safe prime (both p and q are prime)
				// q is already verified by rand.Prime(), so we only need to test p
				qVerified, isSafe := isSafePrime(p, true)
				if isSafe {
					// Try to send result (First-Past-The-Post)
					// Non-blocking write with select
					select {
					case resultCh <- result{p: p, q: qVerified}:
						// This worker won! Cancel all others immediately
						cancelWorkers()
						return
					case <-workerCtx.Done():
						// Another worker already won
						return
					}
				}
			}
		}(i)
	}

	// Wait for first result or context cancellation
	var res result
	select {
	case res = <-resultCh:
		// Got result, cancel all workers
		cancelWorkers()
	case <-ctx.Done():
		// Context cancelled, stop all workers
		cancelWorkers()
		wg.Wait()
		if progressDone != nil {
			close(progressDone)
		}
		return nil, nil, ctx.Err()
	}

	// Wait for all workers to finish cleanup
	wg.Wait()
	
	// Stop progress reporting
	if progressDone != nil {
		close(progressDone)
	}

	if verbose {
		elapsed := time.Since(start)
		attempts := int(totalAttempts.Load())
		sieveRejected := int(totalSieveRejected.Load())
		
		fmt.Fprintf(os.Stderr, "\nGenerated safe prime after %d attempts (%d sieve-rejected) in %v using %d threads\n",
			attempts, sieveRejected, elapsed, threads)
		if attempts > 0 {
			fmt.Fprintf(os.Stderr, "Sieve efficiency: %.1f%% candidates eliminated\n",
				float64(sieveRejected)/float64(attempts)*100)
		}
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
		// Loop through PEM blocks to find DH PARAMETERS
		for {
			block, rest := pem.Decode(data)
			if block == nil {
				return nil, fmt.Errorf("failed to find DH PARAMETERS in PEM data")
			}
			
			// Look for DH PARAMETERS block type
			if block.Type == "DH PARAMETERS" {
				derBytes = block.Bytes
				break
			}
			
			// Continue with remaining data
			data = rest
			if len(data) == 0 {
				return nil, fmt.Errorf("no DH PARAMETERS block found")
			}
		}
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
		P              *big.Int
		G              *big.Int
		PrivateLength  int `asn1:"optional"`
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
	
	// ASN.1 DER encoding rule: add leading 00 if high bit is set (to indicate positive number)
	// This matches OpenSSL's display format
	needsLeadingZero := len(bytes) > 0 && bytes[0]&0x80 != 0
	
	byteCount := 0
	
	// Print leading zero if needed
	if needsLeadingZero {
		fmt.Fprintf(w, "        00:")
		byteCount++
	} else {
		fmt.Fprintf(w, "        ")
	}
	
	// Print actual bytes
	for i := 0; i < len(bytes); i++ {
		// Start new line every 15 bytes
		if byteCount > 0 && byteCount%15 == 0 {
			fmt.Fprintf(w, "\n        ")
		}
		
		fmt.Fprintf(w, "%02x", bytes[i])
		byteCount++
		
		// Add colon separator (except for last byte)
		if i < len(bytes)-1 || (i == len(bytes)-1 && byteCount%15 == 0) {
			fmt.Fprintf(w, ":")
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

	// For safe primes with known Q, verify generator order
	if params.Q != nil {
		// Verify Q is prime
		if !params.Q.ProbablyPrime(20) {
			return fmt.Errorf("Q is not prime")
		}
		
		// Verify P = 2Q + 1
		two := big.NewInt(2)
		expectedP := new(big.Int).Mul(params.Q, two)
		expectedP.Add(expectedP, one)
		if params.P.Cmp(expectedP) != 0 {
			return fmt.Errorf("P != 2Q + 1")
		}
		
		// Verify generator order: G^Q mod P should NOT equal 1
		// This ensures G generates the full subgroup of order Q
		result := new(big.Int).Exp(params.G, params.Q, params.P)
		if result.Cmp(one) == 0 {
			return fmt.Errorf("generator G has incorrect order (G^Q mod P = 1)")
		}
		
		// Additional check: G^(2Q) mod P should equal 1 (G^(P-1) mod P = 1 by Fermat)
		pMinus1 := new(big.Int).Sub(params.P, one)
		result = new(big.Int).Exp(params.G, pMinus1, params.P)
		if result.Cmp(one) != 0 {
			return fmt.Errorf("generator G fails Fermat test (G^(P-1) mod P != 1)")
		}
	}

	// Basic validation passed
	return nil
}
