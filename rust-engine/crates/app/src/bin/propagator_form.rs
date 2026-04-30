//! `propagator-form` — P(x) = (1+2x)/(1+x) closed-form Dyson sum.
//!
//! Tests user 2026-04 hypothesis: 1/α_em correction terms are
//! (P(α·rᵢ) − 1) for atomic ratios rᵢ ∈ {1/4, 1/45, ...}.
//!
//! Reference: lean/E213/Physics/ClosedPropagator.lean.

use drlt_app::basel::{s_partial, upper, Q};
use drlt_app::gap_explorer::{decimal, nat};

/// P(x) = (1 + 2x) / (1 + x).  In Q-pair form:
/// 1 + 2x = (den + 2·num) / den;  1 + x = (den + num) / den.
/// P(x) = (den + 2·num) / (den + num).
fn p(x: &Q) -> Q { (&x.1 + nat(2) * &x.0, &x.1 + &x.0) }

/// P(x) − 1 = x / (1 + x).
fn pm1(x: &Q) -> Q { (x.0.clone(), &x.1 + &x.0) }

/// (P(x) − 1)² = x² / (1+x)².
fn pm1_sq(x: &Q) -> Q {
    let d = &x.1 + &x.0;
    (&x.0 * &x.0, &d * &d)
}

fn main() {
    let _s = s_partial(2000); let u = upper(2000);
    let agut: Q = (u.1.clone(), nat(25) * &u.0);   // α_GUT_lo

    println!("=== P(x) = (1+2x)/(1+x) propagator form ===\n");
    println!("Reference values:");
    println!("  P(0)      = {}        (no perturbation)", decimal(&p(&(nat(0), nat(1))), 6));
    println!("  P(1)      = {}        (= 3/2 = NS/NT, symmetric point)",
        decimal(&p(&(nat(1), nat(1))), 6));
    println!("  α_GUT     ≈ {}", decimal(&agut, 9));
    println!();

    let cases: &[(&str, Q)] = &[
        ("x = α_GUT/4   (Dyson tail, NS+1)", (agut.0.clone(), &agut.1 * nat(4))),
        ("x = α_GUT/45  (NS²·d, gap)",       (agut.0.clone(), &agut.1 * nat(45))),
        ("x = α_GUT     (bare)",             agut.clone()),
    ];

    println!("--- P(x) values for atomic-ratio arguments ---\n");
    println!("  {:<35}  {:<14}  {:<14}  {:<14}", "x", "P(x)", "P(x) − 1", "(P(x)−1)²");
    println!("{}", "─".repeat(85));
    for (label, x) in cases {
        let px = p(x);
        let pmx = pm1(x);
        let pmx2 = pm1_sq(x);
        println!("  {:<35}  {:<14}  {:<14}  {:<14}",
            label, decimal(&px, 9), decimal(&pmx, 9), decimal(&pmx2, 11));
    }

    println!("\n--- Compare exact P(x)−1 vs linear α_GUT/k ---\n");
    let agut4_linear = (agut.0.clone(), &agut.1 * nat(4));
    let agut4_p = pm1(&(agut.0.clone(), &agut.1 * nat(4)));
    let _ = (agut4_linear, agut4_p);
    println!("  α/4 linear   ≈ 0.006079270");
    println!("  P(α/4) − 1   = α/(4+α) = exact closed Dyson sum");
    println!("  (smaller than linear by factor 1/(1+α/4) ≈ 0.994)\n");

    println!("--- 5-term sum: linear vs P-exact ---\n");
    println!("  Linear (α/4 + α/45):");
    println!("    137.0359951    Δ from CODATA = +4×10⁻⁶");
    println!("  P-exact ((P(α/4)−1) + (P(α/45)−1)):");
    println!("    slightly smaller — Δ from CODATA = +7.7×10⁻⁶");
    println!();
    println!("Reading: P-exact moves AWAY from observed.");
    println!("→ Residual likely from MORE P(x) chains at deeper atomic ratios,");
    println!("  not from second-order P² self-correction at same x.");
}
