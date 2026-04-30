//! `triple-coupling` — strong/EM/weak from K_{3,2}^{(2)} cohomology.
//!
//!  1/α_em = 60·ζ(2) + 30 + 25/3 + α_GUT/4 + α_GUT/45
//!  1/α_3  = 8 + 1/2 − α_GUT
//!  1/α_2  = 30 − 1/2 + 3·α_GUT

use drlt_app::basel::{s_partial, upper, Q};
use drlt_app::gap_explorer::{decimal, nat};
use num_bigint::BigUint;

const D: u64 = 5;

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let num = if l >= r { l - r } else { BigUint::from(0u32) };
    (num, &a.1 * &b.1)
}
fn mul_n(a: &Q, n: u64) -> Q { (&a.0 * nat(n), a.1.clone()) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(2000);
    let s = s_partial(n); let u = upper(n);
    let np1 = nat(n + 1);
    let agut_lo: Q = (u.1.clone(), nat(D*D) * &u.0);
    let agut_hi: Q = (s.1.clone(), nat(D*D) * &s.0);

    let c60 = nat(60);
    let t1 = (&c60*&s.0*&np1 + &c60*&s.1, &s.1*&np1);
    let t2 = (nat(30), nat(1));
    let t3 = (nat(25), nat(3));
    let t4 = (agut_lo.0.clone(), &agut_lo.1 * nat(4));
    let t5 = (agut_lo.0.clone(), &agut_lo.1 * nat(45));
    let inv_em = add_q(&add_q(&add_q(&add_q(&t1, &t2), &t3), &t4), &t5);

    let half = (nat(1), nat(2));
    let strong_int = add_q(&(nat(8), nat(1)), &half);
    let inv_a3 = sub_q(&strong_int, &agut_hi);

    let weak_int = sub_q(&(nat(30), nat(1)), &half);
    let three_agut = mul_n(&agut_lo, 3);
    let inv_a2 = add_q(&weak_int, &three_agut);

    println!("=== Triple coupling decomposition (N = {n}) ===\n");
    println!("--- 1/α_em (H^1+...+H^4 Taylor path-impedance) ---");
    println!("  60·ζ(2)   ≈ {}   [12·d edges, H¹]", decimal(&t1, 6));
    println!("  30        = 30           [chiral split disc.]");
    println!("  25/3      ≈ {}    [d²/NS projection]", decimal(&t3, 6));
    println!("  α_GUT/4   ≈ {}     [tetra 4-bd, H²]", decimal(&t4, 9));
    println!("  α_GUT/45  ≈ {}     [(10 C 2) cross, H⁴]", decimal(&t5, 9));
    println!("  Σ        = {}    CODATA 137.035999100",
        decimal(&inv_em, 9));
    println!("\n--- 1/α_3 (strong, A-confinement) ---");
    println!("  8 + 3/6 − α_GUT");
    println!("  Σ        = {}     PDG 1/α_s(MZ) ≈ 8.476",
        decimal(&inv_a3, 6));
    println!("\n--- 1/α_2 (weak, chiral-bd crossing) ---");
    println!("  (31−1) − 1/2 + 3·α_GUT");
    println!("  Σ        = {}     PDG 1/α_2(MZ) ≈ 29.6",
        decimal(&inv_a2, 6));
    println!("\nQED 3 phenomena geometric origin:");
    println!("  √α (vertex)  : H¹ — single A→B edge amplitude");
    println!("  v/c ∝ α      : H² — d²→NS face bottleneck");
    println!("  α² (fine ss) : H⁴ — hinge crosstalk (C(3,3)−C(2,3))");
}
