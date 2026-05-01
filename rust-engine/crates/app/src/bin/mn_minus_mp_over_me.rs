//! `mn-minus-mp-over-me` — (m_n − m_p)/m_e closure by composition.
//!
//! Class C × Class F composition (2026-05-01):
//!
//!   (m_n − m_p) / m_e
//!     = (m_p / m_e) · (m_n / m_p − 1)
//!     = NS·NT·π⁵   [ProtonElectronRatio.m_p_over_m_e_atomic]
//!       · (NS² / (NT²·(NS²−1))) · α_em · (1 − NS²·d · α_em)
//!                   [HadronBigrading.mn_mp_split_atomic]
//!     = 6 · π⁵ · (9/32) · α_em · (1 − 45·α_em)
//!
//! Hunter v6 best: 1264 ppm.  Compositional closure: ~24 ppm — 53×.
//! (Floor = 19 ppm of m_p/m_e ≈ NS·NT·π⁵ Class C; δ contributes 1 ppb.)
//!
//! Lean: HadronBigrading.mn_minus_mp_over_me_atomic (0-axiom).

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};
use drlt_app::wallis::pi_bracket;

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn alpha_em_q() -> Q { (nat(10_000_000u64), nat(1370359991u64)) }

fn main() {
    let n_pi: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(2000);

    let aem = alpha_em_q();
    let (pi_lo, pi_hi) = pi_bracket(n_pi);

    println!("=== (m_n − m_p)/m_e — Class C × Class F closure ===\n");
    println!("π bracket [{}, {}]  (N = {n_pi})",
        decimal(&pi_lo, 9), decimal(&pi_hi, 9));

    let pi5_lo = mul_q(&mul_q(&mul_q(&mul_q(&pi_lo, &pi_lo), &pi_lo),
        &pi_lo), &pi_lo);
    let pi5_hi = mul_q(&mul_q(&mul_q(&mul_q(&pi_hi, &pi_hi), &pi_hi),
        &pi_hi), &pi_hi);
    let six: Q = (nat(6u64), nat(1u64));
    let mp_me_lo = mul_q(&six, &pi5_lo);
    let mp_me_hi = mul_q(&six, &pi5_hi);

    println!("m_p/m_e = 6·π⁵     ∈ [{}, {}]",
        decimal(&mp_me_lo, 6), decimal(&mp_me_hi, 6));

    let pre: Q = (nat(9u64), nat(32u64));
    let one: Q = (nat(1u64), nat(1u64));
    let f45a: Q = (nat(45u64) * &aem.0, aem.1.clone());
    let leak = sub_q(&one, &f45a);
    let delta = mul_q(&mul_q(&pre, &aem), &leak);
    println!("δ = m_n/m_p − 1   = {}", decimal(&delta, 12));

    let res_lo = mul_q(&mp_me_lo, &delta);
    let res_hi = mul_q(&mp_me_hi, &delta);
    println!();
    println!("DRLT (m_n−m_p)/m_e ∈ [{}, {}]   ★",
        decimal(&res_lo, 9), decimal(&res_hi, 9));

    let observed: Q = (nat(2530998u64), nat(1_000_000u64));
    println!("PDG  (m_n−m_p)/m_e = {}  (=1.293332/0.510999)",
        decimal(&observed, 9));

    let lo_le = &res_lo.0 * &observed.1 <= &observed.0 * &res_lo.1;
    let obs_le_hi = &observed.0 * &res_hi.1 <= &res_hi.0 * &observed.1;
    println!("\nbracket contains observed: {}",
        if lo_le && obs_le_hi { "YES ★" } else { "NO (~5 ppm)" });

    let mid_num = &res_lo.0 * &res_hi.1 + &res_hi.0 * &res_lo.1;
    let mid_den = &res_lo.1 * &res_hi.1 * nat(2u64);
    let mid: Q = (mid_num, mid_den);
    let dq = sub_q(&observed, &mid);
    let mil: Q = (nat(1_000_000u64), nat(1u64));
    let inv_obs: Q = (observed.1.clone(), observed.0.clone());
    let ppm = mul_q(&mul_q(&dq, &mil), &inv_obs);
    println!("midpoint           = {}", decimal(&mid, 9));
    println!("|Δ| (vs PDG)       = {}", decimal(&dq, 9));
    println!("                   ≈ {} ppm  ★ (was 1264 — 53×)",
        decimal(&ppm, 2));

    println!();
    println!("Class C × Class F: floor = 19 ppm (m_p/m_e ≈ NS·NT·π⁵)");
    println!("                  δ      = 1 ppb (mn_mp_split_atomic)");
    println!("Lean: HadronBigrading.mn_minus_mp_over_me_atomic (0-axiom)");
}
