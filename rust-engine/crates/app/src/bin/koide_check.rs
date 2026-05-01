//! `koide-check` — Koide formula numerical verification.
//!
//! Q := (m_e + m_μ + m_τ) / (√m_e + √m_μ + √m_τ)²
//!
//! Empirical (CODATA 2022): Q ≈ 0.66666... ≈ 2/3.
//! DRLT identification (2026-04-30): Q = NT/NS = 2/3 atomically.
//!
//! Lean: `Physics.KoideFormula.koide_atomic` (0-axiom).
//!
//! Lepton masses + √-roots stored as high-precision rationals.

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn main() {
    println!("=== Koide formula check — 2/3 = NT/NS structural ===\n");

    // CODATA 2022 lepton masses (MeV, scaled to integer):
    let m_e:   Q = (nat(510998950u64),    nat(1_000_000_000u64));
    let m_mu:  Q = (nat(10565837550u64),  nat(100_000_000u64));
    let m_tau: Q = (nat(177686),          nat(100));

    println!("CODATA 2022:");
    println!("  m_e  = {} MeV", decimal(&m_e, 9));
    println!("  m_μ  = {} MeV", decimal(&m_mu, 8));
    println!("  m_τ  = {} MeV", decimal(&m_tau, 4));

    let sum_m: Q = add_q(&add_q(&m_e, &m_mu), &m_tau);
    println!("Σ m_l = {} MeV\n", decimal(&sum_m, 6));

    // High-precision √m values (10-digit, externally computed):
    let sqrt_me:   Q = (nat(7148419820u64),  nat(10_000_000_000u64));
    let sqrt_mmu:  Q = (nat(1027902600u64),  nat(100_000_000u64));
    let sqrt_mtau: Q = (nat(4215281939u64),  nat(100_000_000u64));

    println!("√m_e  ≈ {}", decimal(&sqrt_me, 9));
    println!("√m_μ  ≈ {}", decimal(&sqrt_mmu, 8));
    println!("√m_τ  ≈ {}\n", decimal(&sqrt_mtau, 8));

    let sum_sqrt: Q = add_q(&add_q(&sqrt_me, &sqrt_mmu), &sqrt_mtau);
    let sum_sqrt_sq: Q = mul_q(&sum_sqrt, &sum_sqrt);
    println!("(Σ √m_l)² = {}\n", decimal(&sum_sqrt_sq, 6));

    // Q_koide = sum_m / (sum_sqrt)²
    let q_koide: Q = (sum_m.0.clone() * &sum_sqrt_sq.1,
                      sum_m.1.clone() * &sum_sqrt_sq.0);
    let drlt: Q = (nat(2), nat(3));

    println!("Q (Koide)          = {}", decimal(&q_koide, 9));
    println!("DRLT (NT/NS = 2/3) = {}    ★", decimal(&drlt, 9));

    let dq = sub_q(&q_koide, &drlt);
    let ppm = mul_q(&mul_q(&dq, &(nat(1_000_000), nat(1))),
                    &(drlt.1.clone(), drlt.0.clone()));
    println!("|Δ|                = {}", decimal(&dq, 9));
    println!("                   ≈ {} ppm  ★\n", decimal(&ppm, 1));

    println!("Geometric reading:");
    println!("  v := (√m_e, √m_μ, √m_τ),  diag := (1, 1, 1)");
    println!("  cos²(∠) = (Σ√m)² / (3 Σm) = 1/(3·Q) = 1/2");
    println!("  ⇒ angle(v, diag) = 45°  (1+i unit-vector direction)");
    println!();
    println!("Atomic identification:  Q = NT / NS = 2 / 3.");
    println!("Class C (bare lattice invariant).  Same (NS, NT) split");
    println!("that gives 3 generations via C(NS, NT) = 3.");
    println!();
    println!("Lean cite: KoideFormula.koide_atomic (0-axiom)");
}
