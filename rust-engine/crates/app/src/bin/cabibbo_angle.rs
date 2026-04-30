//! `cabibbo-angle` — sin θ_C = D / (D² − D + c) = 5/22 (pure rational)
//! Lean: CabibboAngle.lean.
//!
//! Bare value: 5/22 = 0.2273   (no transcendentals, no inputs)
//! Observed:   0.2257 ± 0.0011 (PDG V_us)
//! Δ ≈ +0.7% — Ξ correction from CabibboAngle.lean closes further.

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};

fn main() {
    let d = 5u64;
    let c = 2u64;
    let denom = d * d - d + c;
    println!("=== Cabibbo angle from K_{{3,2}}^{{(2)}} ===\n");
    println!("Lattice atoms: d = {d}, c = {c}");
    println!("Denominator   : d² − d + c = 25 − 5 + 2 = {}", denom);
    println!();

    // sin θ_C = d / (d² − d + c) = 5/22
    let sin_theta: Q = (nat(d), nat(denom));
    println!("DRLT sin θ_C  = {}/{} = {}    ★",
        d, denom, decimal(&sin_theta, 6));

    // Observed: 0.2257 (PDG)
    let observed: Q = (nat(2257), nat(10000));
    println!("Observed |V_us| = {}  (PDG V_us = sin θ_C)",
        decimal(&observed, 4));

    let l = &sin_theta.0 * &observed.1;
    let r = &observed.0 * &sin_theta.1;
    let dn = if l >= r { l - r } else { r - l };
    let diff: Q = (dn, &sin_theta.1 * &observed.1);
    let pct: Q = (&diff.0 * nat(10000) * &observed.1, &diff.1 * &observed.0);
    println!("|Δ|            ≈ {} ({} ×10⁻⁴)",
        decimal(&diff, 6), decimal(&pct, 2));

    println!();
    println!("★ Pure rational 5/22 from atomic primitives — no inputs.");
    println!("   Ξ correction from Lean CabibboAngle.lean closes further.");
    println!();
    println!("Lean cite: CabibboAngle.sin_theta_C_bare (0-axiom)");
}
