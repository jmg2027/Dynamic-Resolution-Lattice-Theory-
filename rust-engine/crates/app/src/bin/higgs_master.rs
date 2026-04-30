//! `higgs-master` — full Higgs sector (Lean HiggsMaster.lean):
//!
//!   m_H = v_H · (1 + α_GUT) · (1 − α_GUT/d) / c
//!   λ_H = (m_H/(√2·v_H))² = ((1+α_GUT)(1−α_GUT/d)/c)² / 2
//!
//! Two α_GUT corrections (face BC + embedding suppression).
//! Same atomic ratios (c=2, d=5).  v_H scale set externally.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);

    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== Higgs sector — full m_H + λ_H (N = {n}) ===\n");
    println!("α_GUT          ≈ {}", decimal(&agut, 12));

    // Factor 1: (1 + α_GUT) = (a.0 + a.1, a.1)
    let f1: Q = (&agut.0 + &agut.1, agut.1.clone());
    // Factor 2: (1 - α_GUT/d) = (5·a.1 - a.0, 5·a.1)
    let f2: Q = (&agut.1 * nat(5) - &agut.0, &agut.1 * nat(5));

    println!("(1 + α_GUT)    ≈ {}", decimal(&f1, 9));
    println!("(1 − α_GUT/d)  ≈ {}", decimal(&f2, 9));

    // m_H/v_H = f1 · f2 / c
    let mh_vh = mul_q(&f1, &f2);
    let mh_vh_c: Q = (mh_vh.0.clone(), &mh_vh.1 * nat(2));
    println!("m_H/v_H = (·)/c ≈ {}", decimal(&mh_vh_c, 9));

    // λ_H = (m_H/v_H)² / 2 = ((·)/c)² / 2
    let mh_vh_c_sq = mul_q(&mh_vh_c, &mh_vh_c);
    let lambda_h: Q = (mh_vh_c_sq.0.clone(), &mh_vh_c_sq.1 * nat(2));
    let observed_lambda: Q = (nat(1294), nat(10000));

    println!();
    println!("λ_H = (m_H/v_H)²/2 = {} ★", decimal(&lambda_h, 9));
    println!("Observed (PDG)     = {}  (m_H/v from CODATA)",
        decimal(&observed_lambda, 6));

    let l = &observed_lambda.0 * &lambda_h.1;
    let r = &lambda_h.0 * &observed_lambda.1;
    let diff_num = if l > r { l - r } else { r - l };
    let diff: Q = (diff_num, &observed_lambda.1 * &lambda_h.1);
    let pct: Q = (&diff.0 * nat(10_000) * &observed_lambda.1,
                  &diff.1 * &observed_lambda.0);
    println!("|Δ|                ≈ {}", decimal(&diff, 8));
    println!("                   ≈ {} ×10⁻⁴ relative", decimal(&pct, 2));

    println!();
    println!("Comparison:");
    println!("  λ_H simple (1+α_GUT)²/8           ≈ 0.13115  → 1.4% off");
    println!("  λ_H full ((1+α_GUT)(1-α/d)/c)²/2  ≈ above    ★");
    println!("\nLean cite: HiggsMaster.higgs_master_atomic (0-axiom)");
}
