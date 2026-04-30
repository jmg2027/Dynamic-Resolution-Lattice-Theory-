//! `overlap-series` — K_{3,2}^{(2)} instance overlap multiplicities.
//!
//! M(N, k) = #{unordered 5-subset pairs sharing k vertices}
//!         = C(N,5) · C(5,k) · C(N−5, 5−k) / 2   (k < 5).

use drlt_app::gap_explorer::{decimal, nat};
use drlt_app::basel::Q;
use num_bigint::BigUint;

fn binom(n: u64, k: u64) -> BigUint {
    if k > n { return BigUint::from(0u32); }
    let mut r = BigUint::from(1u32);
    let k = k.min(n - k);
    for i in 0..k { r = &r * (n - i); r /= i + 1; }
    r
}

fn overlap(n: u64, k: u64) -> BigUint {
    if k > 5 || k > n { return BigUint::from(0u32); }
    if k == 5 { return binom(n, 5); }
    binom(n, 5) * binom(5, k) * binom(n - 5, 5 - k) / 2u32
}

fn per_inst(n: u64, k: u64) -> Q {
    if k > 5 || k > n { return (nat(0), nat(1)); }
    if k == 5 { return (nat(1), nat(1)); }
    (binom(5, k) * binom(n - 5, 5 - k), nat(2))
}

fn main() {
    println!("=== K_{{3,2}}^{{(2)}} overlap multiplicities ===\n");
    println!("{:>5} | {:>10} {:>12} {:>14} {:>16} {:>18} {:>20}",
        "N", "C(N,5)", "M(4)", "M(3)", "M(2)", "M(1)", "M(0)");
    println!("{}", "─".repeat(102));
    for n in [5u64, 6, 7, 8, 10, 15, 41, 100, 1000] {
        print!("{:>5} | {:>10}", n, binom(n, 5));
        for k in (0..=4).rev() { print!(" {:>14}", overlap(n, k)); }
        println!();
    }

    println!("\n=== Per-instance (M / C(N,5)) ===\n");
    for n in [10u64, 41, 100, 1000, 10000] {
        print!("N={:>5} |", n);
        for k in (0..=4).rev() {
            print!(" k{}={:>11}", k, decimal(&per_inst(n, k), 3));
        }
        println!();
    }

    println!("\n=== α_GUT^(5−k) · per-inst — geometric series test ===\n");
    // α_GUT = 6/(25π²) ≈ 0.024318.  ℚ approx: 600/24674.
    let agut: Q = (nat(600), nat(24674));
    for n in [10u64, 41, 100, 1000] {
        print!("N={:>5} |", n);
        for k in (0..=4).rev() {
            let pi = per_inst(n, k);
            let mut w: Q = (nat(1), nat(1));
            for _ in 0..(5 - k) { w = (&w.0 * &agut.0, &w.1 * &agut.1); }
            let p: Q = (&pi.0 * &w.0, &pi.1 * &w.1);
            print!(" k{}={:>13}", k, decimal(&p, 8));
        }
        println!();
    }

    println!("\nv2 residuals to compare:");
    println!("  1/α_em ~ 1×10⁻⁸    1/α_3 ~ 3×10⁻⁵    1/α_2 ~ 3×10⁻³");
}
