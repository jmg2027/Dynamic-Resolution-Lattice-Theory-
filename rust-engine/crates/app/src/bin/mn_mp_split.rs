//! `mn-mp-split` — m_n/m_p Class F atomic split (Path c, 2026-05-01).
//!
//! Isospin-symmetric base w_u = w_d on K_{25} ⇒ leading m_n/m_p = 1.
//! K_{25} cup-chain perturbation (Class F δ_glue):
//!
//!   m_n/m_p − 1 = [NS²/(NT²(NS²−1))] · α_em · (1 − NS²·d · α_em)
//!               = (9 / 32) · α_em · (1 − 45·α_em)
//!
//! Atomic counts:
//!   9  = NS²                  (3-quark u-spin slot count)
//!   32 = NT²·(NS²−1) = 2^d    (chiral × color generator volume)
//!   45 = NS²·d                (cup-chain α² coefficient)
//!
//! Locked 0-axiom in Physics.HadronBigrading.mn_mp_split_atomic.

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn alpha_em_q() -> Q {
    // 1/α_em = 137.0359991 (CODATA, 10-digit anchor)
    (nat(10_000_000u64), nat(1370359991u64))
}

fn main() {
    let aem = alpha_em_q();

    println!("=== m_n/m_p Class F atomic split (Path c) ===\n");
    println!("Base (isospin chiral limit): w_u = w_d ⇒ m_n/m_p|_lead = 1");
    println!("K_25 cup-chain coefficient:");
    println!("  δ = (NS²/(NT²·(NS²−1))) · α_em · (1 − NS²·d · α_em)\n");

    let pre: Q = (nat(9u64), nat(32u64));
    let one: Q = (nat(1u64), nat(1u64));
    let forty_five_alpha: Q = (nat(45u64) * &aem.0, aem.1.clone());
    let leak = sub_q(&one, &forty_five_alpha);
    let delta = mul_q(&mul_q(&pre, &aem), &leak);
    let pred = add_q(&one, &delta);

    println!("Components:");
    println!("  NS²/(NT²(NS²−1))  = 9/32 = {}", decimal(&pre, 9));
    println!("  α_em              ≈ {}", decimal(&aem, 12));
    println!("  1 − 45·α_em       ≈ {}", decimal(&leak, 12));
    println!();
    println!("DRLT m_n/m_p − 1   = {}", decimal(&delta, 12));
    println!("DRLT m_n/m_p       = {}", decimal(&pred, 12));

    // PDG 2022: m_n/m_p = 1.001378419 (σ ≈ 5e-10)
    let observed: Q = (nat(1001378419u64), nat(1_000_000_000u64));
    println!("PDG  m_n/m_p (2022)= {}", decimal(&observed, 12));

    let dq = sub_q(&observed, &pred);
    let mil: Q = (nat(1_000_000u64), nat(1u64));
    let inv_obs: Q = (observed.1.clone(), observed.0.clone());
    let ppm = mul_q(&mul_q(&dq, &mil), &inv_obs);
    println!();
    println!("|Δ|                = {}", decimal(&dq, 12));
    println!("                   ≈ {} ppm  ★", decimal(&ppm, 3));
    println!();

    println!("Atomic decomposition (all 0-axiom, no fudge):");
    println!("  NS²              = 9   (3-quark u-spin slot count)");
    println!("  NT²·(NS²−1)      = 32  (chiral×color volume = 2^d)");
    println!("  NS²·d            = 45  (cup-chain α² coefficient)");
    println!();
    println!("Path (c) finding (2026-05-01): Tier-4 m_n/m_p closes at");
    println!("≤ 1 ppm via the K_{{25}} cup-chain (9/32) on the isospin-");
    println!("symmetric base.  45·α_em is the Class D double cup-product");
    println!("(NS² u-spin × d simplex iter).");
    println!();
    println!("Lean cite: HadronBigrading.mn_mp_split_atomic (0-axiom)");
}
