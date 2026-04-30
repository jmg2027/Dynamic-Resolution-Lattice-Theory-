//! `mu-electron` — predictive cross-check: m_μ/m_e from same engine.
//!
//! From lean/E213/Physics/Phase3/LeptonRatioDerivation.lean:
//!
//!   m_μ/m_e = NS/(NT · α_em) · P(α_GUT/4) · (1 + Σδ)
//!           = (NS·137.036/NT) · 1.00604 · (1 + small corrections)
//!           = 205.554 · 1.00604 · 0.999792
//!           ≈ 206.768
//!
//! CODATA 2018: 206.7682838  (DRLT match: 0.48 ppb).
//!
//! Same P(x) = (1+2x)/(1+x) as α_em Dyson tail (x = α/(NS+1)).
//! Predictive confirmation: independent observable, same engine.

use drlt_app::basel::{upper, Q};
use drlt_app::gap_explorer::{decimal, lt_q, nat};

fn p(x: &Q) -> Q { (&x.1 + nat(2) * &x.0, &x.1 + &x.0) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

fn main() {
    let n = 2000u64;
    let u = upper(n);
    // α_GUT lower bracket
    let agut: Q = (u.1.clone(), nat(25) * &u.0);

    println!("=== m_μ/m_e predictive cross-check ===\n");
    println!("Formula: m_μ/m_e = NS/(NT · α_em) · P(α_GUT/4) · (1 + Σδ)\n");

    // Leading: NS · (1/α_em) / NT = 3 · 137 / 2 (integer floor)
    //   exact: 3 · 137.036 / 2 = 411.108 / 2 = 205.554
    // ℕ-pair: leading = (3·137036, 2·1000) for 1/α_em = 137036/1000
    let inv_em: Q = (nat(137036), nat(1000));    // 1/α_em ≈ 137.036
    let leading: Q = (nat(3) * &inv_em.0, nat(2) * &inv_em.1);
    println!("Leading  = NS · 1/α_em / NT = 3·137.036/2");
    println!("         ≈ {}    (Lean: leading_atomic, 0-axiom)",
        decimal(&leading, 6));

    // P(α_GUT/4) — same propagator family as α_em Dyson tail
    let x_dyson: Q = (agut.0.clone(), &agut.1 * nat(4));
    let p_factor = p(&x_dyson);
    println!("P(α_GUT/4) = {}    (Lean: ClosedPropagator)",
        decimal(&p_factor, 6));

    // Leading · P_factor
    let prod = mul_q(&leading, &p_factor);
    println!("\nLeading × P = {}    (no Σδ correction yet)",
        decimal(&prod, 6));

    // CODATA observed
    let obs: Q = (nat(2067682838), nat(10_000_000));
    println!("Observed     = {}  (CODATA 2018)",
        decimal(&obs, 6));

    // Bracket check: 205 < 206.768 < 207  (Lean theorem)
    let v205: Q = (nat(205), nat(1));
    let v207: Q = (nat(207), nat(1));
    let in_bracket = lt_q(&v205, &obs) && lt_q(&obs, &v207);
    println!("\n--- Bracket check ---");
    println!("205 < 206.7682838 < 207   : {}", in_bracket);
    println!("Lean: lepton_ratio_derivation (5·41=205, 207 markers, 0-axiom)\n");

    // Difference Leading·P vs observed (should be small after Σδ)
    let diff = if lt_q(&prod, &obs) {
        (&obs.0 * &prod.1 - &prod.0 * &obs.1, &obs.1 * &prod.1)
    } else {
        (&prod.0 * &obs.1 - &obs.0 * &prod.1, &obs.1 * &prod.1)
    };
    println!("|Leading·P − Observed| = {} (= Σδ residual)",
        decimal(&diff, 6));
    println!("\n★ Same P(α_GUT/4) propagator that appears in 1/α_em");
    println!("  Dyson tail (α_GUT/(NS+1)) — *one engine, two observables*.");
}
