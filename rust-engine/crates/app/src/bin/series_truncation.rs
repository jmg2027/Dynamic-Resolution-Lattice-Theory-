//! `series-truncation` — test user hypothesis (2026-04):
//!   residual_X = Σ over k-overlap pairs · α_GUT^(5−k) / norm
//! with truncation depth differing per coupling.
//!
//! ⚠ Diagnostic, not certified.  No row in `whitelist.toml` —
//! hypothesis test feeding into Lean development; not a verification.

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

fn main() {
    let agut: Q = (nat(600), nat(24674));
    println!("=== Series truncation test ===\n");
    println!("Per-instance · α_GUT^(5−k) for various N\n");
    println!("{:>5} | {:>13} {:>13} {:>13} {:>13} {:>13}",
        "N", "k=4·α¹", "k=3·α²", "k=2·α³", "k=1·α⁴", "k=0·α⁵");
    println!("{}", "─".repeat(85));
    for n in [7u64, 8, 10, 12, 15, 20, 41] {
        print!("{:>5} |", n);
        for k in (0..=4).rev() {
            let pi = per_inst(n, k);
            let mut w: Q = (nat(1), nat(1));
            for _ in 0..(5 - k) {
                w = (&w.0 * &agut.0, &w.1 * &agut.1);
            }
            let term: Q = (&pi.0 * &w.0, &pi.1 * &w.1);
            print!(" {:>13}", decimal(&term, 8));
        }
        println!();
    }

    println!("\n=== Cumulative sum from k=4 downward (truncation depth) ===\n");
    println!("{:>5} | {:>13} {:>13} {:>13} {:>13} {:>13}",
        "N", "k≥4", "k≥3", "k≥2", "k≥1", "k≥0 (full)");
    println!("{}", "─".repeat(85));
    for n in [7u64, 8, 10, 15, 20, 41, 100, 1000] {
        let mut cum: Q = (nat(0), nat(1));
        print!("{:>5} |", n);
        for k in (0..=4).rev() {
            let pi = per_inst(n, k);
            let mut w: Q = (nat(1), nat(1));
            for _ in 0..(5 - k) {
                w = (&w.0 * &agut.0, &w.1 * &agut.1);
            }
            let term: Q = (&pi.0 * &w.0, &pi.1 * &w.1);
            cum = (&cum.0 * &term.1 + &term.0 * &cum.1, &cum.1 * &term.1);
            print!(" {:>13}", decimal(&cum, 8));
        }
        println!();
    }

    println!("\n=== v2 residuals to compare ===");
    println!("  1/α_em ≈ 3×10⁻⁶   (full N→∞ series)");
    println!("  1/α_3  ≈ 3×10⁻⁵   (DoF-confined: shallow cutoff)");
    println!("  1/α_2  ≈ 3×10⁻³   (DoF + asymmetry: medium cutoff)");
}
