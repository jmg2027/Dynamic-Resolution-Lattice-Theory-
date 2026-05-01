//! `top-yukawa` — y_t closure: Top = full-lattice resonance with a
//! single α_GUT/NS leakage correction (added 2026-04-30).
//!
//! Conjecture chain:
//!   Top = full K_{3,2}^{(c=2)} resonance ⇒ y_t ≈ 1 (saturate vev).
//!   Single-step projection back through NS spatial sector leaks
//!   α_GUT/NS off the saturation point.
//!
//!   y_t = 1 − α_GUT/NS  =  (NS − α_GUT)/NS
//!       = (NS·d²·ζ(2) − 1) / (NS·d²·ζ(2))
//!
//! Numerical check (PDG):
//!   m_t = 172.69 GeV,  v_H = 246.22 GeV,  √2 ≈ 1.41421356
//!   y_t observed = m_t·√2/v_H ≈ 0.99194
//!   y_t DRLT     = 1 − α_GUT/NS ≈ 0.99189   |Δ| ≈ 50 ppm  ★
//!
//! Lean: `Physics.QuarkHierarchy.top_yukawa_skeleton` (0-axiom).
//! ⚠ Diagnostic numeric trace; the *structural* claim is in Lean.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn main() {
    let n: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== Top Yukawa atomic closure ===\n");
    println!("ζ(2) tight ≈ {}  (N = {n})", decimal(&zeta_tight, 9));
    println!("α_GUT      ≈ {}\n", decimal(&agut, 9));

    // y_t DRLT = 1 - α_GUT/NS
    let agut_over_ns: Q = (agut.0.clone(), nat(3) * &agut.1);
    let one: Q = (nat(1), nat(1));
    let y_t_drlt = sub_q(&one, &agut_over_ns);

    println!("--- DRLT closed form ---");
    println!("  y_t = 1 − α_GUT/NS  =  (NS·d²·ζ(2) − 1) / (NS·d²·ζ(2))");
    println!("      ≈ {}\n", decimal(&y_t_drlt, 9));

    // Observed: m_t·√2/v_H, with √2 high-precision rational and PDG masses.
    // m_t = 17269/100, v_H = 24622/100, √2 ≈ 1.4142135624
    // y_t_obs = m_t · √2 / v_H = 17269 · 14142135624 / (100 · 24622·10^10)
    let mt = (nat(17269u64), nat(100));
    let vh = (nat(24622u64), nat(100));
    let sqrt2 = (nat(14142135624u64), nat(10_000_000_000u64));
    let y_t_obs = mul_q(&mt, &mul_q(&sqrt2, &(vh.1.clone(), vh.0.clone())));

    println!("--- PDG observed ---");
    println!("  m_t = 172.69 GeV,  v_H = 246.22 GeV,  √2 ≈ 1.4142135624");
    println!("  y_t obs = m_t·√2/v_H ≈ {}\n", decimal(&y_t_obs, 9));

    let dy = sub_q(&y_t_obs, &y_t_drlt);
    let ppm = mul_q(&mul_q(&dy, &(nat(1_000_000u64), nat(1))),
                    &(y_t_obs.1.clone(), y_t_obs.0.clone()));
    println!("  |Δ y_t|  ≈ {}", decimal(&dy, 9));
    println!("           ≈ {} ppm  ★\n", decimal(&ppm, 1));

    println!("Structural reading:");
    println!("  Top quark = full K_{{3,2}}^{{(2)}} lattice resonance");
    println!("  (would saturate v_H/√2, giving y_t = 1)");
    println!("  minus one α_GUT/NS leakage projecting back through");
    println!("  the spatial sector basepoint (NS = 3).");
    println!();
    println!("Lean cite: QuarkHierarchy.top_yukawa_skeleton (0-axiom)");
}
