//! `higgs-quartic` — λ_H Higgs quartic coupling from K_{3,2}^{(2)}.
//! Lean: HiggsQuartic.lean
//!
//!   √(2λ) = f_occ(AABB) · V(x_H) = (1/c) · (1 + α_GUT)
//!   λ_H   = ((1 + α_GUT) / c)² / 2
//!
//! Leading (α_GUT → 0):
//!   λ_H = 1/(2c²) = 1/8 = 0.125
//!   (= 1/α_3 reciprocal — *Higgs coupling = strong gauge coupling*)
//!
//! With α_GUT correction:
//!   λ_H = (1 + α_GUT)² / 8
//!
//! Same atomic ratios as α_em / m_μ/m_e: c=2 (multiplicity).

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

    println!("=== λ_H Higgs quartic (N = {n}) ===\n");
    println!("α_GUT          ≈ {}", decimal(&agut, 12));

    // 1 + α_GUT = (α.0 + α.1, α.1)
    let one_plus_agut: Q = (&agut.0 + &agut.1, agut.1.clone());
    println!("1 + α_GUT      ≈ {}", decimal(&one_plus_agut, 9));

    // (1 + α_GUT)²
    let sq = mul_q(&one_plus_agut, &one_plus_agut);

    // λ_H = (1 + α_GUT)² / 8
    let lambda_h: Q = (sq.0.clone(), &sq.1 * nat(8));
    let lambda_leading: Q = (nat(1), nat(8));    // = 0.125

    println!();
    println!("Leading λ_H = 1/(2c²) = 1/8 = {}",
        decimal(&lambda_leading, 6));
    println!("                       = 1/α_3 (★ Higgs ↔ strong gauge!)");
    println!();
    println!("λ_H = (1+α_GUT)²/8     = {}    ★", decimal(&lambda_h, 9));

    // Observed: λ_H ≈ 0.1294 from m_H = 125.25 GeV, v = 246 GeV
    //   λ = m_H² / (2·v²) ≈ 125.25² / (2·246²) ≈ 0.1294
    let observed: Q = (nat(1294), nat(10000));    // 0.1294
    println!("Observed (PDG) ≈ {} (from m_H/v)", decimal(&observed, 6));

    let l = &observed.0 * &lambda_h.1;
    let r = &lambda_h.0 * &observed.1;
    let diff_num = if l > r { l - r } else { r - l };
    let diff: Q = (diff_num, &observed.1 * &lambda_h.1);
    let pct: Q = (&diff.0 * nat(10_000) * &observed.1,
                  &diff.1 * &observed.0);
    println!("|Δ|             ≈ {}", decimal(&diff, 8));
    println!("                ≈ {} ×10⁻⁴ relative", decimal(&pct, 2));

    println!();
    println!("Universal P(x) connection:");
    println!("  V(x) = 1 + 2x   (= numerator of P(x) = (1+2x)/(1+x))");
    println!("  At x = α_GUT/2:  V = 1 + α_GUT  →  λ_H formula above.");
    println!("\nLean cite: HiggsQuartic.lambda_leading_denom (= 8 = 1/α_3)");
}
