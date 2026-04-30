//! `mu-electron` — m_μ/m_e full Σδ closure (Lean MuOverE.lean):
//!   m_μ/m_e = (NS/NT)·(1/α_em) · P · (1 + δ₁ + δ₂ + δ₃)
//!   P  = 1/(1 − α_GUT/(NS+1))     [Dyson geometric, x = α/4]
//!   δ₁ = −α_em·α_GUT/(1−α_GUT)    [Cabibbo Ξ]
//!   δ₂ = −α_GUT²/(d²−1)            [adjoint SU(5)]
//!   δ₃ = −α_em²·α_GUT              [double-mixing]

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 - &b.0 * &a.1, &a.1 * &b.1) }

fn main() {
    // 1/α_em ≈ 137036/1000 → α_em = 1000/137036
    let inv_em: Q = (nat(137036), nat(1000));
    let em: Q = (inv_em.1.clone(), inv_em.0.clone());
    // α_GUT ≈ 600/24674 (= 6/(25π²) approx)
    let agut: Q = (nat(600), nat(24674));

    println!("=== m_μ/m_e full closure (Σδ corrections) ===\n");
    let leading: Q = (nat(3) * &inv_em.0, nat(2) * &inv_em.1);
    println!("Leading  (NS·1/α_em/NT)  = {}", decimal(&leading, 9));

    // P = 1/(1 - α_GUT/(NS+1))  with x = α_GUT/4
    //   1 - x = (4·α_GUT.1 - α_GUT.0, 4·α_GUT.1)
    //   1/(1-x) = (4·α_GUT.1, 4·α_GUT.1 - α_GUT.0)
    let four_aden = nat(4) * &agut.1;
    let p_geom: Q = (four_aden.clone(), &four_aden - &agut.0);
    println!("P (geom, 1/(1−α/4))      = {}", decimal(&p_geom, 9));

    // δ₁ = α_em · α_GUT / (1 − α_GUT)
    let one_minus_agut: Q = (&agut.1 - &agut.0, agut.1.clone());
    let em_mul_agut = mul_q(&em, &agut);
    // δ₁ = em·agut · 1/(1-agut) = em·agut · (agut.1, agut.1 - agut.0)
    let delta1: Q = (&em_mul_agut.0 * &one_minus_agut.1,
                     &em_mul_agut.1 * &one_minus_agut.0);
    // δ₂ = α_GUT² / (d² − 1) = α_GUT² / 24
    let agut_sq = mul_q(&agut, &agut);
    let delta2: Q = (agut_sq.0.clone(), &agut_sq.1 * nat(24));
    // δ₃ = α_em² · α_GUT
    let em_sq = mul_q(&em, &em);
    let delta3: Q = mul_q(&em_sq, &agut);

    println!("|δ₁| (Cabibbo)            = {}", decimal(&delta1, 9));
    println!("|δ₂| (adjoint SU(5))      = {}", decimal(&delta2, 9));
    println!("|δ₃| (double-mix)         = {}", decimal(&delta3, 9));

    // Σ|δ| (all are negative; sum magnitudes then subtract from 1)
    let sum_delta = add_q(&add_q(&delta1, &delta2), &delta3);
    println!("Σ|δ|                       = {}", decimal(&sum_delta, 9));

    // 1 + Σδ = 1 − Σ|δ|
    let one_plus_sigma_delta = sub_q(&(nat(1), nat(1)), &sum_delta);
    println!("(1 + Σδ)                   = {}", decimal(&one_plus_sigma_delta, 9));

    // Final = Leading · P · (1+Σδ)
    let mid = mul_q(&leading, &p_geom);
    let final_q = mul_q(&mid, &one_plus_sigma_delta);
    let codata: Q = (nat(2067682838), nat(10_000_000));

    println!("\n  Leading · P              = {}", decimal(&mid, 9));
    println!("  Leading · P · (1+Σδ)     = {}    ★", decimal(&final_q, 9));
    println!("  CODATA 2018              = {}", decimal(&codata, 9));

    // |diff| with abs handling (codata may be smaller than DRLT)
    let l = &codata.0 * &final_q.1;
    let r = &final_q.0 * &codata.1;
    let diff_num = if l > r { l - r } else { r - l };
    let diff: Q = (diff_num, &codata.1 * &final_q.1);
    println!("\n  |CODATA − DRLT|           ≈ {}", decimal(&diff, 11));
    // ppb = |Δ|/CODATA × 10⁹
    let ppb: Q = (&diff.0 * nat(1_000_000_000) * &codata.1,
                  &diff.1 * &codata.0);
    println!("                            ≈ {} ppb", decimal(&ppb, 1));
    println!("\nLean cite: MuOverE.mu_over_e_simplicial_pattern (0-axiom)");
}
