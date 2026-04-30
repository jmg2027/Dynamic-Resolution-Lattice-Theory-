//! `neutrino-mixing` — PMNS angles + δ_CP from K_{3,2}^{(2)}.
//! Lean: NeutrinoMixing.lean.
//!
//!   sin²θ₁₂ = 1/NS = 1/3 (leading) − corrections
//!   sin²θ₂₃ = 1/NT = 1/2 (leading, maximal) + corrections
//!   sin²θ₁₃ = α_GUT · (1 − 4·α_GUT)  (small parameter)
//!   δ_CP    = 180° + 360°/(d²−1) = 180° + 360°/24 = 195°
//!
//! Atomic primitives only: NS=3, NT=2, d²−1=24, α_GUT.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l >= r { l - r } else { num_bigint::BigUint::from(0u32) };
    (n, &a.1 * &b.1)
}

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== PMNS mixing from K_{{3,2}}^{{(2)}} ===\n");
    println!("α_GUT  ≈ {}", decimal(&agut, 12));

    // sin²θ₁₂ leading = 1/NS = 1/3
    let sin12_lead: Q = (nat(1), nat(3));
    println!("\nsin²θ₁₂ leading (= 1/NS = 1/3) = {}",
        decimal(&sin12_lead, 6));
    println!("  Observed: 0.307 ± 0.013  (PDG global fit)");

    // sin²θ₂₃ leading = 1/NT = 1/2 (maximal mixing)
    let sin23_lead: Q = (nat(1), nat(2));
    println!("\nsin²θ₂₃ leading (= 1/NT = 1/2) = {}    (maximal)",
        decimal(&sin23_lead, 6));
    println!("  Observed: 0.572 (NH best-fit, near 0.5 maximal)");

    // sin²θ₁₃ = α_GUT · (1 − 4·α_GUT)
    let four_agut: Q = (&agut.0 * nat(4), agut.1.clone());
    let one = (nat(1), nat(1));
    let one_minus_4agut = sub_q(&one, &four_agut);
    let sin13 = mul_q(&agut, &one_minus_4agut);
    println!("\nsin²θ₁₃ = α_GUT·(1−4·α_GUT) = {}    ★", decimal(&sin13, 9));
    let observed_13: Q = (nat(220), nat(10000));   // 0.0220
    println!("  Observed: {}  (PDG)", decimal(&observed_13, 5));
    let l = &sin13.0 * &observed_13.1; let r = &observed_13.0 * &sin13.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &sin13.1 * &observed_13.1);
    let sigma: Q = (&diff.0 * nat(100) * &observed_13.1,
                    &diff.1 * &observed_13.0);
    println!("  |Δ| ≈ {} ({} % relative)",
        decimal(&diff, 6), decimal(&sigma, 2));

    // δ_CP = 180° + 360°/(d²−1) = 180° + 15° = 195°
    let dcp_corr: Q = (nat(360), nat(24));    // 360°/24
    let dcp_total: Q = (
        nat(180) * dcp_corr.1.clone() + dcp_corr.0.clone(),
        dcp_corr.1.clone(),
    );
    println!("\nδ_CP = 180° + 360°/(d²−1) = 180° + 360°/24");
    println!("                          = 180° + 15° = {}°",
        decimal(&dcp_total, 4));
    println!("  Observed: ≈ 197° (T2K/NOvA, large uncertainty)");
    println!("\nLean cite: NeutrinoMixing (sin²θ₁₃, δ_CP, 0-axiom)");
}
