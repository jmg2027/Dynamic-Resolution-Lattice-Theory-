//! `higgs-vacuum` — v_H = (d+1)·M_Pl / d^(d²) (Lean HiggsVacuum.lean).
//!
//! Hierarchy explanation: v_H ≪ M_Pl is *natural* — lattice depth
//! d^(d²) = 5^25 is huge.  Not fine-tuning.
//!
//! v_H = 6·M_Pl/5^25 ≈ 245.6 GeV  (observed ≈ 246 GeV, +0.16%)

use num_bigint::BigUint;

fn pow_big(base: u64, exp: u32) -> BigUint {
    let b = BigUint::from(base);
    let mut r = BigUint::from(1u32);
    for _ in 0..exp { r = &r * &b; }
    r
}

fn main() {
    let d = 5u32;
    let d_sq = d * d;            // 25 (Gram channels)
    let numer = d + 1;           // 6 (bipartite edges = NS·NT)
    let denom = pow_big(d as u64, d_sq);    // 5^25

    println!("=== Higgs vacuum hierarchy v_H/M_Pl ===\n");
    println!("Atoms: d = {}, d² = {} (Gram channels), d+1 = {}",
        d, d_sq, numer);
    println!();
    println!("v_H/M_Pl = (d+1) / d^(d²) = {} / {}", numer, denom);
    println!("        = 6 / 5^25");
    println!();
    println!("d^(d²) = 5^25 = {}", denom);

    // Compute v_H as M_Pl ≈ 1.22×10^19 GeV → v_H ≈ 246 GeV
    // 6 * 1.22e19 / 5^25 = 7.32e19 / 2.98e17 = 245.6 GeV
    // Or as ratio: v_H = (M_Pl) · 6 / 5^25
    println!();
    println!("Numerical (M_Pl ≈ 1.22 × 10¹⁹ GeV):");
    println!("  v_H = 6 · 1.22e19 / 5^25");
    println!("      ≈ 245.6 GeV   (observed: 246 GeV, +0.16%)");

    println!();
    println!("★ Hierarchy from atomic exponent ★");
    println!("  No fine-tuning: v_H ≪ M_Pl is *natural* lattice cardinality.");
    println!("  d² = 25 lattice levels, each d-fold branching = d^(d²).");
    println!();
    println!("  log₁₀(M_Pl/v_H) = log₁₀(d^(d²)/(d+1))");
    println!("                  ≈ d²·log₁₀(d) − log₁₀(d+1)");
    println!("                  ≈ 25 · 0.699 − 0.778 ≈ 16.7");

    println!("\nLean cite: HiggsVacuum.hier_num + hier_exp (0-axiom)");
}
