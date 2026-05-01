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

    // sin²θ₁₂ Pythagorean: NT²/(NS²+NT²) = 4/13
    let sin12_pyt: Q = (nat(4), nat(13));
    println!("\nsin²θ₁₂ = NT²/(NS²+NT²) = 4/13 = {}",
        decimal(&sin12_pyt, 9));
    println!("  PDG = 0.307 ± 0.013  (42000 ppm experimental)");
    println!("  ★ Pythagorean rational from (NS=3, NT=2) — no α correction");
    println!("  tan θ₁₂ = NT/NS = 2/3 (atomic ratio)");
    let obs_12: Q = (nat(307), nat(1000));
    let l = &sin12_pyt.0 * &obs_12.1; let r = &obs_12.0 * &sin12_pyt.1;
    let dn = if l > r { l - r } else { r - l };
    let diff_12: Q = (dn, &sin12_pyt.1 * &obs_12.1);
    let ppm_12: Q = (&diff_12.0 * nat(1_000_000) * &obs_12.1,
                     &diff_12.1 * &obs_12.0);
    println!("  ppm = {}  (was 8500 ppm via 1/NS leading)",
        decimal(&ppm_12, 1));

    // sin²θ₂₃ leading = 1/NT = 1/2 (maximal mixing)
    let sin23_lead: Q = (nat(1), nat(2));
    println!("\nsin²θ₂₃ leading (= 1/NT = 1/2) = {}    (maximal)",
        decimal(&sin23_lead, 6));
    println!("  Observed: 0.572 (NH best-fit, near 0.5 maximal)");

    // sin²θ₁₃ tighter: α_GUT·(1−NT²·α_GUT)·(1+NS·NT·α_GUT²)
    //                = α_GUT·(1 − 4·α_GUT)·(1 + 6·α_GUT²)
    let four_agut: Q = (&agut.0 * nat(4), agut.1.clone());
    let one = (nat(1), nat(1));
    let one_minus_4agut = sub_q(&one, &four_agut);
    let agut_sq = mul_q(&agut, &agut);
    let six_agut_sq: Q = (&agut_sq.0 * nat(6), agut_sq.1.clone());
    let one_plus_6agut2: Q =
        (&one.0 * &six_agut_sq.1 + &six_agut_sq.0 * &one.1,
         &one.1 * &six_agut_sq.1);
    let sin13 = mul_q(&mul_q(&agut, &one_minus_4agut), &one_plus_6agut2);
    println!("\nsin²θ₁₃ = α_GUT·(1−NT²·α_GUT)·(1+NS·NT·α_GUT²)");
    println!("        = α_GUT·(1−4·α_GUT)·(1+6·α_GUT²)");
    println!("        = {}    ★", decimal(&sin13, 9));
    let observed_13: Q = (nat(2203), nat(100000));   // PDG 0.02203
    println!("  PDG: {} ± 0.00058 (NuFIT)", decimal(&observed_13, 5));
    let l = &sin13.0 * &observed_13.1; let r = &observed_13.0 * &sin13.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &sin13.1 * &observed_13.1);
    let ppm: Q = (&diff.0 * nat(1_000_000) * &observed_13.1,
                  &diff.1 * &observed_13.0);
    println!("  |Δ| ≈ {} ({} ppm — was 3550 ppm)",
        decimal(&diff, 8), decimal(&ppm, 1));

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
    println!("\nLean cite: NeutrinoMixing.sin2_13_v2_atomic (0-axiom)");
}
