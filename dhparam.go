// A fully compatible OpenSSL dhparam implementation in Go with multi-threaded acceleration support.
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
//   - First uses Miller-Rabin with base 2
//   - Then uses additional pseudoprime tests
//
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

// Extended prime sieve for faster combined filtering
var (
	primesSieve []*big.Int
	primesMod   []uint64
)

func init() {
	// Generate primes up to 10000 using Sieve of Eratosthenes
	limit := 10000
	isPrime := make([]bool, limit)
	for i := 2; i < limit; i++ {
		isPrime[i] = true
	}

	for i := 2; i*i < limit; i++ {
		if isPrime[i] {
			for j := i * i; j < limit; j += i {
				isPrime[j] = false
			}
		}
	}

	// Collect primes into arrays
	primesSieve = make([]*big.Int, 0, 1229)
	primesMod = make([]uint64, 0, 1229)

	for i := 2; i < limit; i++ {
		if isPrime[i] {
			primesSieve = append(primesSieve, big.NewInt(int64(i)))
			primesMod = append(primesMod, uint64(i))
		}
	}
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

// fastCheckCombinedSieve checks if q or 2q+1 is divisible by small primes.
// Returns true if CANDIDATE IS BAD (composite), false if likely prime.
func fastCheckCombinedSieve(q *big.Int) bool {
	// Logic:
	// 1. If q % prime == 0, then q is composite -> reject
	// 2. If (2q + 1) % prime == 0, then p is composite -> reject
	//    Formula: 2q ≡ -1 (mod prime) → 2q ≡ prime - 1 (mod prime) → q ≡ (prime-1)/2 (mod prime)
	//    So we only need to check if q % prime == (prime-1)/2

	// Note: big.Int.Rem for small int64 is still orders of magnitude faster than Miller-Rabin
	// although there is some allocation overhead in the loop

	var rem big.Int

	for i, pVal := range primesMod {
		// Skip 2 since q is always odd
		if pVal == 2 {
			continue
		}

		// Calculate r = q % prime
		rem.Rem(q, primesSieve[i])
		r := rem.Uint64()

		// Check 1: Is q divisible by this prime?
		if r == 0 {
			return true
		}

		// Check 2: Is p = 2q+1 divisible by this prime?
		// Equivalent to checking if r == (prime-1)/2
		if r == (pVal-1)/2 {
			return true
		}
	}

	return false
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

	// Calculate recommended private key length following OpenSSL's algorithm
	privateLength := calculatePrivateLength(bits)

	return &DHParams{
		P:             p,
		G:             g,
		Q:             q,
		PrivateLength: privateLength,
	}, nil
}

// calculatePrivateLength calculates the recommended private key length
// following OpenSSL's implementation in crypto/dh/dh_gen.c and crypto/rsa/rsa_lib.c
//
// This ensures the private key's strength aligns with the overall security of the parameters,
// balancing against attacks like Number Field Sieve (NFS) and Pollard's rho.
//
// Algorithm:
// 1. Estimate security bits of the modulus using NIST SP 800-56B rev. 2
// 2. Compute: length = ((2 * security_bits + 24) / 25) * 25
//
// The formula doubles security bits (to match subgroup security against Pollard's rho),
// adds a 24-bit buffer, then rounds down to a multiple of 25 bits.
//
// Examples:
// - 1024-bit: security=80 bits → recommended=175 bits
// - 2048-bit: security=112 bits → recommended=225 bits
// - 3072-bit: security=128 bits → recommended=275 bits
// - 7680-bit: security=192 bits → recommended=400 bits
func calculatePrivateLength(modulusBits int) int {
	// Step 1: Estimate security bits using NIST SP 800-56B rev. 2 formula
	// This is implemented in ossl_ifc_ffc_compute_security_bits()
	securityBits := computeSecurityBits(modulusBits)

	// Step 2: Calculate recommended private length
	// Formula from OpenSSL crypto/dh/dh_gen.c:
	// length = ((2 * security_bits + 24) / 25) * 25
	// This doubles security bits, adds 24-bit buffer, rounds down to multiple of 25

	length := ((2*securityBits + 24) / 25) * 25

	return length
}

// computeSecurityBits estimates the security strength in bits for a given modulus size
// Based on OpenSSL's ossl_ifc_ffc_compute_security_bits() in crypto/rsa/rsa_lib.c
// Uses NIST SP 800-56B rev. 2 Appendix D
//
// For a modulus of n bits, the security against NFS attacks is estimated using:
// E = (1.923 * ∛(n * ln(2)) * (ln(n * ln(2)))^(2/3) - 4.69) / ln(2)
//
// However, OpenSSL uses hardcoded values from NIST standards for common sizes
// with rounding: y = (computed_value + 4) & ~7 (rounds to nearest multiple of 8, upward)
//
// The values below are BREAKPOINTS (not the only valid sizes):
// - Any modulus >= 15360 bits gets 256-bit security rating
// - Any modulus >= 7680 but < 15360 bits gets 192-bit security rating
// - And so on...
//
// Examples:
// - 1024-bit: 80-bit security
// - 1536-bit: 80-bit security (still in the 1024-7680 range)
// - 2048-bit: 112-bit security
// - 3000-bit: 112-bit security (in the 2048-3072 range)
// - 4096-bit: 128-bit security
func computeSecurityBits(modulusBits int) int {
	// These are BREAKPOINTS defining security levels
	// Any size can be used; it will map to the appropriate security level
	if modulusBits >= 15360 {
		return 256
	}
	if modulusBits >= 7680 {
		return 192
	}
	if modulusBits >= 3072 {
		return 128
	}
	if modulusBits >= 2048 {
		return 112
	}
	if modulusBits >= 1024 {
		return 80 // Conservative NIST rating; actual NFS security ~79.95 bits
	}

	// For smaller sizes (not recommended for production)
	if modulusBits >= 512 {
		return 64
	}

	return 56 // Absolute minimum
}

// generateSafePrimeWithContext generates a safe prime using single thread with context support
// Optimized version: generate random q, then filter both q and p=2q+1 simultaneously
func generateSafePrimeWithContext(ctx context.Context, bits int, callback ProgressCallback, verbose bool) (*big.Int, *big.Int, error) {
	start := time.Now()
	attempts := 0
	sieveRejected := 0

	// Pre-allocate memory
	q := new(big.Int)
	p := new(big.Int)
	one := big.NewInt(1)

	// Calculate bytes needed for q (bits-1 bits)
	qBytesLen := (bits - 1 + 7) / 8
	b := make([]byte, qBytesLen)

	for {
		// Check context cancellation
		select {
		case <-ctx.Done():
			return nil, nil, ctx.Err()
		default:
		}

		attempts++

		// 1. Generate random candidate q (just random bytes, no primality test yet)
		_, err := rand.Read(b)
		if err != nil {
			return nil, nil, err
		}

		// Ensure highest bit is set (guarantee correct bit length)
		b[0] |= 0x80
		// Ensure lowest bit is set (guarantee odd number)
		b[len(b)-1] |= 1

		q.SetBytes(b)

		// Handle bit length precision (if not multiple of 8)
		if q.BitLen() > bits-1 {
			q.Rsh(q, uint(q.BitLen()-(bits-1)))
			if q.Bit(0) == 0 { // Might become even after shift
				q.Or(q, one)
			}
		}

		// 2. Combined Sieve: filter both q and p=2q+1 simultaneously
		// This is VERY fast and filters out 99.9% of candidates
		if fastCheckCombinedSieve(q) {
			sieveRejected++
			if verbose && attempts%2000 == 0 {
				fmt.Fprintf(os.Stderr, ".")
			}
			continue
		}

		// 3. At this point, neither q nor 2q+1 has small factors
		// Check if q is prime (20 rounds sufficient)
		if !q.ProbablyPrime(20) {
			if verbose && attempts%100 == 0 {
				fmt.Fprintf(os.Stderr, ".")
			}
			continue
		}

		// 4. Calculate p = 2q + 1
		p.Lsh(q, 1)   // p = 2*q
		p.Add(p, one) // p = p + 1

		// 5. Check if p is prime (cryptographic strength, 64 rounds)
		// Success rate is much higher now!
		if p.ProbablyPrime(64) {
			if verbose {
				elapsed := time.Since(start)
				fmt.Fprintf(os.Stderr, "\nGenerated safe prime after %d attempts (%d sieve-rejected) in %v\n",
					attempts, sieveRejected, elapsed)
				if attempts > 0 {
					fmt.Fprintf(os.Stderr, "Sieve efficiency: %.1f%% candidates eliminated\n",
						float64(sieveRejected)/float64(attempts)*100)
				}
			}
			return p, q, nil
		}

		// Progress reporting
		if callback != nil && attempts%1000 == 0 {
			callback(attempts, sieveRejected)
		}
		if verbose && attempts%2000 == 0 {
			fmt.Fprintf(os.Stderr, ".")
		}
	}
}

// generateSafePrimeParallelWithContext generates a safe prime using multiple threads with First-Past-The-Post model
// Optimized version: generate random q, then filter both q and p=2q+1 simultaneously
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

	// Progress reporting goroutine (centralized output)
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

			// Pre-allocate memory for this worker
			q := new(big.Int)
			p := new(big.Int)
			one := big.NewInt(1)

			// Calculate bytes needed for q
			qBytesLen := (bits - 1 + 7) / 8
			b := make([]byte, qBytesLen)

			for {
				// Check context cancellation FIRST
				select {
				case <-workerCtx.Done():
					return
				default:
				}

				// 1. Generate random candidate q
				_, err := rand.Read(b)
				if err != nil {
					continue
				}

				// Ensure highest bit is set and number is odd
				b[0] |= 0x80
				b[len(b)-1] |= 1

				q.SetBytes(b)

				// Handle bit length precision
				if q.BitLen() > bits-1 {
					q.Rsh(q, uint(q.BitLen()-(bits-1)))
					if q.Bit(0) == 0 {
						q.Or(q, one)
					}
				}

				// Atomic increment for precise counting
				totalAttempts.Add(1)

				// 2. Combined Sieve: filter both q and p=2q+1
				if fastCheckCombinedSieve(q) {
					totalSieveRejected.Add(1)
					continue
				}

				// 3. Check if q is prime (20 rounds)
				if !q.ProbablyPrime(20) {
					continue
				}

				// 4. Calculate p = 2q + 1
				p.Lsh(q, 1)
				p.Add(p, one)

				// 5. Check if p is prime (64 rounds for cryptographic strength)
				if p.ProbablyPrime(64) {
					// Try to send result (First-Past-The-Post)
					select {
					case resultCh <- result{p: new(big.Int).Set(p), q: new(big.Int).Set(q)}:
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
