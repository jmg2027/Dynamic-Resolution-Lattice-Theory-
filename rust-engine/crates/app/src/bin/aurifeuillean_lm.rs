//! `aurifeuillean-lm` — Compute Aurifeuillean L_m, M_m for
//! `Phi_{10m^2}(5) = L_m^2 - 5*M_m^2` in `Z[sqrt(5)]`.
//!
//! Used to populate `AurifeuilleanLUnbounded.lean` chain (m = 1, 3, 7
//! embedded; m = 11 attempted, infeasible at this scale).
//!
//! Modes:
//!   · `phi <n>`                     — evaluate Phi_n(5) and print
//!   · `verify <N> <L> <M>`          — check L^2 - 5*M^2 == N
//!   · `cornacchia <N>`              — try Cornacchia-style search
//!                                     for (L, M) with L^2 - 5*M^2 = N
//!   · `l7-check`                    — verify known L_7 round-trip
//!   · `l11-attempt`                 — compute Phi_1210(5)
//!
//! ## Algorithm landscape for finding (L, M)
//!
//! Given Phi_n(5) (very large integer), find integers (L, M) with
//! L^2 - 5*M^2 = Phi_n(5).  Equivalent to: find element of given
//! norm in `Z[sqrt(5)]`.
//!
//! ### Feasible at this scale (m ≤ 7)
//!
//! 1. **PARI/GP `bnfisnorm`** — class group + norm equation.
//!    For Q(sqrt(5)) class number is 1, so reduces to factoring
//!    N over Z[sqrt(5)].  PARI factors N via Pollard rho / ECM.
//!    Works for `n ≤ 490` (m ≤ 7) in seconds.
//!
//! 2. **sympy `factor(Phi_n, extension=sqrt(5))`** — polynomial
//!    factorization over algebraic extension via Trager's
//!    algorithm.  Yields the half-degree factor polynomial A(y);
//!    evaluating at y=5 gives `(L + M*sqrt(5))/D` for some `D ∈ Z`.
//!    Works for `n ≤ 490` in minutes.
//!
//! ### Intractable at this scale (m ≥ 11) without specialized tools
//!
//! 3. **Direct factorization of Phi_n(5)** — requires GNFS for
//!    308-digit numbers (Phi_1210(5) has digits ≈ 308).  No
//!    general-purpose tool in this container.  Trial division on
//!    primes `≡ 1 (mod n)` finds small factors only (we found
//!    389621 as one factor of Phi_1210(5), remaining 302 digits).
//!
//! 4. **LLL reduction** — construct lattice with shortest vector
//!    encoding (L, M).  Requires sqrt(5) mod N, which needs the
//!    factorization of N (back to step 3).
//!
//! ### Theoretical paths (require additional infrastructure)
//!
//! 5. **Stevens-Brent explicit polynomial formula** — there is a
//!    closed-form polynomial L_m(x), M_m(x) for each m (built via
//!    the cyclotomic Galois orbit over Q(sqrt(5))).  Constructing
//!    L_m(x), M_m(x) explicitly for general m requires
//!    polynomial-ring arithmetic over Q(sqrt(5))[x], same
//!    complexity as sympy's factor approach.  No shortcut to
//!    avoid the polynomial-factorization step.
//!
//! 6. **Brent's published Aurifeuillean tables** — Brent and
//!    Cohen have published m-indexed (L_m, M_m) tables for
//!    various bases.  Not accessible from this container.
//!
//! Lean cite: AurifeuilleanLUnbounded.Lval / L_norm_m{1,3,7}

use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::env;

/// Compute the n-th cyclotomic polynomial Phi_n evaluated at integer
/// `base`, returned as `BigUint`.
///
/// Uses the recursive formula:
///   `Phi_n(x) * prod_{d | n, d < n} Phi_d(x) = x^n - 1`
///
/// Computes via the Mobius-inversion-equivalent recursion.
fn phi_at(n: u64, base: u64) -> BigUint {
    // Special cases for small n
    if n == 1 { return BigUint::from(base) - BigUint::one(); }

    // Compute x^n - 1
    let base_big = BigUint::from(base);
    let mut num = BigUint::one();
    for _ in 0..n {
        num = &num * &base_big;
    }
    num = num - BigUint::one(); // x^n - 1

    // Compute product of Phi_d(base) for d | n, d < n
    let mut denom = BigUint::one();
    for d in 1..n {
        if n % d == 0 {
            denom = &denom * &phi_at(d, base);
        }
    }

    // Phi_n(base) = (x^n - 1) / prod
    num / denom
}

/// Integer square root via Newton's method on BigUint.
fn isqrt(n: &BigUint) -> BigUint {
    if n.is_zero() { return BigUint::zero(); }
    let bits = n.bits();
    let mut x: BigUint = BigUint::one() << ((bits / 2) + 1);
    loop {
        let y: BigUint = (&x + n / &x) >> 1;
        if y >= x { return x; }
        x = y;
    }
}

/// Verify L^2 - 5*M^2 == N.
fn verify_norm(n: &BigUint, l: &BigUint, m: &BigUint) -> bool {
    let lhs = l * l;
    let rhs = m * m * BigUint::from(5u32) + n;
    lhs == rhs
}

/// Try to find (L, M) with L^2 - 5*M^2 = N by brute search over
/// M near isqrt(N/5).  Returns Some((L, M)) if found.
///
/// Search strategy: M ranges from 0 to `max_iters`, for each M check
/// if `N + 5*M^2` is a perfect square.  This is the simplest possible
/// approach and works for cases where M is small relative to N.
///
/// For Aurifeuillean L_m: M_m ~ L_m / sqrt(5) ~ sqrt(N/5)·c, which
/// is huge for large m.  So this brute search is not useful for
/// m ≥ 7.  Included for completeness and L_1 verification.
fn cornacchia_brute(n: &BigUint, max_iters: u64) -> Option<(BigUint, BigUint)> {
    let five = BigUint::from(5u32);
    for m_val in 0..max_iters {
        let m = BigUint::from(m_val);
        let candidate = n + &five * &m * &m;
        let l = isqrt(&candidate);
        if &l * &l == candidate {
            return Some((l, m));
        }
    }
    None
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: {} <phi N | verify N L M | cornacchia N | l7-check | l11-attempt>", args[0]);
        std::process::exit(1);
    }

    match args[1].as_str() {
        "phi" => {
            let n: u64 = args[2].parse().expect("n must be a positive integer");
            let v = phi_at(n, 5);
            println!("Phi_{}(5) = {}", n, v);
            println!("digits = {}", v.to_string().len());
        }
        "verify" => {
            let n: BigUint = args[2].parse().expect("N must be BigUint");
            let l: BigUint = args[3].parse().expect("L must be BigUint");
            let m: BigUint = args[4].parse().expect("M must be BigUint");
            let ok = verify_norm(&n, &l, &m);
            println!("L^2 - 5*M^2 == N: {}", ok);
            if !ok {
                let lhs = &l * &l;
                let rhs = &m * &m * BigUint::from(5u32) + &n;
                println!("  L^2 = {}", lhs);
                println!("  5*M^2 + N = {}", rhs);
            }
        }
        "cornacchia" => {
            let n: BigUint = args[2].parse().expect("N must be BigUint");
            let max_iters: u64 = if args.len() > 3 {
                args[3].parse().unwrap_or(10_000_000)
            } else {
                10_000_000
            };
            println!("Searching for (L, M) with L^2 - 5*M^2 = {} (max M = {})", n, max_iters);
            match cornacchia_brute(&n, max_iters) {
                Some((l, m)) => {
                    println!("FOUND: L = {}", l);
                    println!("       M = {}", m);
                    println!("Verify: {}", verify_norm(&n, &l, &m));
                }
                None => {
                    println!("Not found in M range [0, {})", max_iters);
                }
            }
        }
        "l7-check" => {
            // Verify the known L_7 = 52742989966756323681507284226843205703532077081025251160441
            // M_7 = 4669562488132553079590607027544755956542605909071800599664
            // Phi_490(5) verifies via PARI.
            let n = phi_at(490, 5);
            let l: BigUint = "52742989966756323681507284226843205703532077081025251160441"
                .parse().unwrap();
            let m: BigUint = "4669562488132553079590607027544755956542605909071800599664"
                .parse().unwrap();
            println!("Phi_490(5) digits = {}", n.to_string().len());
            println!("L_7 (59 digits)  = {}", l);
            println!("M_7 (58 digits)  = {}", m);
            println!("L^2 - 5*M^2 == Phi_490(5): {}", verify_norm(&n, &l, &m));
        }
        "l11-attempt" => {
            // m = 11: n = 2*5*11^2 = 1210
            // Phi_1210(5) is ~308 digits
            println!("Computing Phi_1210(5)...");
            let n = phi_at(1210, 5);
            println!("Phi_1210(5) digits = {}", n.to_string().len());
            println!("Phi_1210(5) = {}", n);
            println!("\nNote: Cornacchia brute search infeasible for this size (M ~ 10^150).");
            println!("Use PARI/GP bnfisnorm or Brent's Aurifeuillean tables for L_11.");
        }
        cmd => {
            eprintln!("Unknown command: {}", cmd);
            std::process::exit(1);
        }
    }
}
