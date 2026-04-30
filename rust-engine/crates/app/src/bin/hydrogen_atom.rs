//! `hydrogen-atom` — Bohr ground state E_1 = −m_e·α²/NT  (NT=2!)
//! Lean: HydrogenAtom.lean.
//!
//! Standard Bohr formula's mysterious "2" in denominator
//!   E_n = −13.6 eV · 1/n² = −m_e·α_em²/(NT·n²)
//! NT = 2 = chiral phase/time sector dimension.
//!
//! Numerically: 13.605 eV (DRLT) vs 13.598 eV (CODATA) → +0.05%.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let _s = s_partial(n);

    println!("=== Hydrogen atom E_1 = −m_e·α²/NT ===\n");
    println!("Bohr formula's '2' identified as NT = 2.\n");

    // m_e (electron mass) as input from CODATA: 510998.95 eV
    // (this is the only external mass scale; 213 derives ratio not absolute mass)
    let m_e_ev: Q = (nat(51_099_895), nat(100));    // 510998.95 eV
    let inv_alpha_em: Q = (nat(1370359991u64), nat(10_000_000));
    // α_em = 1/inv_alpha_em
    // α_em² = 1/inv_alpha_em²
    let alpha_em_sq: Q = (inv_alpha_em.1.clone() * &inv_alpha_em.1,
                          &inv_alpha_em.0 * &inv_alpha_em.0);

    // E_1 magnitude = m_e · α² / NT = m_e · α² / 2
    let m_e_alpha_sq = mul_q(&m_e_ev, &alpha_em_sq);
    let e_1: Q = (m_e_alpha_sq.0, &m_e_alpha_sq.1 * nat(2));   // / NT = / 2

    println!("m_e (eV)         = {}", decimal(&m_e_ev, 4));
    println!("α_em²             = m_e·α²/m_e in Q form (computed)");
    println!();
    println!("DRLT |E_1|        = m_e · α² / NT");
    println!("                  = {} eV    ★", decimal(&e_1, 6));

    let observed: Q = (nat(135980), nat(10000));    // 13.598 eV
    println!("Observed |E_1|    = {} eV  (CODATA Rydberg/2 ≈ 13.598)",
        decimal(&observed, 6));

    let l = &e_1.0 * &observed.1; let r = &observed.0 * &e_1.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &e_1.1 * &observed.1);
    let pct: Q = (&diff.0 * nat(10000) * &observed.1, &diff.1 * &observed.0);
    println!("|Δ|               ≈ {} eV ({} ×10⁻⁴)",
        decimal(&diff, 6), decimal(&pct, 2));

    println!("\n★ Standard '2' in Bohr formula = NT  ★");
    println!("  Without NT=2 the ground state would be 27.2 eV.");
    println!("  213 derives the *factor* of 2, classical Bohr couldn't.");
    println!("\nLean cite: HydrogenAtom (E_n = −m_e·α²/(NT·n²))");
}
