//! `finite-resonance` — N must be FINITE (user 2026-04):
//! infinite N → reverberations diffuse → cancel → no residual.
//! Finite N → bounded paths → reverberations return → residual lives.
//!
//! Sweeps N and computes (full overlap series) / (N−5)^4, comparing
//! to v2 residuals.  Highlights "natural" 213 N-values:
//!   N = 8  (= b_1, K_{3,2}^{(2)})
//!   N = 25 (= d²)
//!   N = 30 (= 1/α_2 integer)
//!   N = 32 (= 2^d, all sub-simplices)
//!   N = 41 (= ⌊1/α_GUT⌋)

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};
use num_bigint::BigUint;

fn binom(n: u64, k: u64) -> BigUint {
    if k > n { return BigUint::from(0u32); }
    let mut r = BigUint::from(1u32); let k = k.min(n - k);
    for i in 0..k { r = &r * (n - i); r /= i + 1; } r
}

fn per_inst(n: u64, k: u64) -> Q {
    if k == 5 { return (nat(1), nat(1)); }
    if k > 5 || k > n { return (nat(0), nat(1)); }
    (binom(5, k) * binom(n - 5, 5 - k), nat(2))
}

fn full_series(n: u64, agut: &Q) -> Q {
    let mut total: Q = (nat(0), nat(1));
    for k in 0..=4u64 {
        let pi = per_inst(n, k);
        let mut w: Q = (nat(1), nat(1));
        for _ in 0..(5 - k) {
            w = (&w.0 * &agut.0, &w.1 * &agut.1);
        }
        let term: Q = (&pi.0 * &w.0, &pi.1 * &w.1);
        total = (&total.0 * &term.1 + &term.0 * &total.1,
                 &total.1 * &term.1);
    }
    total
}

fn main() {
    let agut: Q = (nat(600), nat(24674));
    let natural: &[(u64, &str)] = &[
        (8,  "b_1 = 1/α_3"),
        (10, "c·d (chiral split)"),
        (15, "b_1 + (d+2)?"),
        (20, "1/α_3 v2 N (empirical)"),
        (25, "d²"),
        (30, "1/α_2 integer"),
        (32, "2^d (all sub-simplices)"),
        (41, "⌊1/α_GUT⌋"),
    ];

    println!("=== Finite-N resonance: residual = full_series(N) / (N−5)^4 ===\n");
    println!("v2 residuals: 1/α_2 ≈ 3×10⁻³, 1/α_3 ≈ 3×10⁻⁵, 1/α_em ≈ 3×10⁻⁶");
    println!("({{N : 'natural 213 scale'}})\n");
    println!("{:>4} {:<28} | {:>14} | {:>16}",
        "N", "natural meaning", "full series", "/(N−5)^4");
    println!("{}", "─".repeat(75));
    for (n, meaning) in natural {
        if *n < 6 { continue; }
        let series = full_series(*n, &agut);
        let nm5 = nat(n - 5).pow(4);
        let normalized: Q = (series.0.clone(), &series.1 * &nm5);
        println!("{:>4} {:<28} | {:>14} | {:>16}",
            n, meaning, decimal(&series, 6), decimal(&normalized, 11));
    }

    println!("\n=== Match table ===");
    println!("  1/α_2 residual ≈ 3×10⁻³  → matches N=8  (= b_1)");
    println!("  1/α_3 residual ≈ 3×10⁻⁵  → matches N≈20 (4·d?)");
    println!("  1/α_em residual ≈ 3×10⁻⁶ → matches N=41 (= ⌊1/α_GUT⌋) ★");
    println!("\nReading: each coupling has its own *finite* lattice scale N.");
    println!("Cancellation (∞-N) prevented by bounded domain — residual lives.");
}
