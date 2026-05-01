//! `mu-electron` — m_μ/m_e full Σδ closure (Lean MuOverE.lean):
//!   m_μ/m_e = (NS/NT)·(1/α_em) · P · (1 + δ₁ + δ₂ + δ₃)
//!   P  = 1/(1 − α_GUT/(NS+1)),  δ₁=−α_em·α_GUT/(1−α_GUT)
//!   δ₂ = −α_GUT²/(d²−1),         δ₃ = −α_em²·α_GUT
//!
//! α_GUT defined *precisely* as bracket: 1/(d²·ζ(2)) where
//!   ζ(2) ∈ [S(N) + 1/(N+1), S(N) + 1/N]  (Real213 bracket).
//! Using tight lower S(N)+1/(N+1) gives ppb-scale precision.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(10000);

    // ζ(2) tight bracket: S(N) + 1/(N+1) ≤ ζ(2) ≤ S(N) + 1/N.
    let s = s_partial(n);
    // tight upper of ζ(2) lower bracket: S(N) + 1/(N+1) (closest to ζ(2))
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    // α_GUT = 1/(d²·ζ(2)) = (zeta.1, 25·zeta.0)
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);
    // 1/α_em from CODATA 2018: 137.0359991, written precisely.
    let inv_em: Q = (nat(1370359991u64), nat(10_000_000));
    let em: Q = (inv_em.1.clone(), inv_em.0.clone());

    println!("=== m_μ/m_e (precise α_GUT bracket, N = {n}) ===\n");
    println!("ζ(2) ≈ {}  (tight from S(N)+1/(N+1))", decimal(&zeta_tight, 12));
    println!("α_GUT ≈ {}", decimal(&agut, 12));
    println!();

    let leading: Q = (nat(3) * &inv_em.0, nat(2) * &inv_em.1);
    let four_aden = nat(4) * &agut.1;
    let p_geom: Q = (four_aden.clone(), &four_aden - &agut.0);

    let one_minus_agut: Q = (&agut.1 - &agut.0, agut.1.clone());
    let em_mul_agut = mul_q(&em, &agut);
    let delta1: Q = (&em_mul_agut.0 * &one_minus_agut.1,
                     &em_mul_agut.1 * &one_minus_agut.0);
    let agut_sq = mul_q(&agut, &agut);
    let delta2: Q = (agut_sq.0.clone(), &agut_sq.1 * nat(24));
    let em_sq = mul_q(&em, &em);
    let delta3: Q = mul_q(&em_sq, &agut);

    let sum_delta = add_q(&add_q(&delta1, &delta2), &delta3);
    let one_q: Q = (nat(1), nat(1));
    // (1 - sum_delta) since all δ are negative
    let one_plus_sigma: Q = ((&one_q.0 * &sum_delta.1) - &sum_delta.0,
                             one_q.1 * sum_delta.1);
    let final_q = mul_q(&mul_q(&leading, &p_geom), &one_plus_sigma);
    let codata: Q = (nat(2067682838), nat(10_000_000));

    println!("Leading = NS·(1/α_em)/NT  = {}", decimal(&leading, 9));
    println!("P (geom)                  = {}", decimal(&p_geom, 9));
    println!("(1 + Σδ)                   = {}", decimal(&one_plus_sigma, 12));
    println!();
    println!("DRLT m_μ/m_e              = {} ★", decimal(&final_q, 9));
    println!("CODATA 2018               = {}", decimal(&codata, 9));

    let l = &codata.0 * &final_q.1;
    let r = &final_q.0 * &codata.1;
    let diff_num = if l > r { l - r } else { r - l };
    let diff: Q = (diff_num, &codata.1 * &final_q.1);
    let ppb: Q = (&diff.0 * nat(1_000_000_000) * &codata.1,
                  &diff.1 * &codata.0);
    println!("|CODATA − DRLT|            ≈ {}", decimal(&diff, 12));
    println!("                           ≈ {} ppb", decimal(&ppb, 2));
    println!();
    println!("Lean cite: MuOverE.mu_over_e_simplicial_pattern (0-axiom)");
}
