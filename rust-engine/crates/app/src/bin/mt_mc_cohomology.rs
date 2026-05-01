//! `mt-mc-cohomology` — m_t/m_c via the quark-chain decomposition,
//! contrasting with the "Top = full lattice resonance" reading.
//!
//! Chain composition:
//!   m_t/m_b = 1/α_GUT      = d²·ζ(2)             (existing DRLT)
//!   m_b/m_c = NS·(1 + α_GUT·NT²)                  (added 2026-04-30)
//!   ⇒ m_t/m_c = NS·(1/α_GUT + NT²) = NS·d²·ζ(2) + NS·NT²
//!             = 75·ζ(2) + 12
//!
//! Cohomology reading of the closed form:
//!   75·ζ(2)  = NS·d²·Basel  (3 generations × d² channels × Σ 1/n²)
//!   12       = NS·NT²       (3 generations × chiral phase volume)
//!
//! Compare to 1/α_em = 60·ζ(2) + 30 + 25/3 + α/4 + α/45.  Both are
//! ζ(2)-leading atomic polynomials, but with *different* coefficients
//! (75 vs 60, 12 vs 38⅓).  The "double 137" near-coincidence is a
//! numerical proximity, NOT a structural identity — m_t/m_c carries
//! its own cohomology polynomial.
//!
//! Lean: `Physics.QuarkHierarchy.mt_mc_chain_atomic` (0-axiom).

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn main() {
    let n: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== m_t/m_c — quark chain vs full-lattice readings ===\n");
    println!("ζ(2) tight ≈ {} (N = {n})", decimal(&zeta_tight, 9));
    println!("α_GUT      ≈ {}\n", decimal(&agut, 9));

    // Chain: m_t/m_c = NS·d²·ζ(2) + NS·NT² = 75·ζ(2) + 12
    let chain: Q = add_q(
        &mul_q(&(nat(75), nat(1)), &zeta_tight),
        &(nat(12), nat(1)),
    );

    println!("--- DRLT chain composition ---");
    println!("  m_t/m_b = d²·ζ(2)            = 1/α_GUT");
    println!("  m_b/m_c = NS·(1 + α_GUT·NT²)");
    println!("  product = NS·d²·ζ(2) + NS·NT²");
    println!("          = 75·ζ(2) + 12");
    println!("          ≈ {}\n", decimal(&chain, 6));

    let inv_em: Q = (nat(1370359991u64), nat(10_000_000));
    let pdg: Q = (nat(17269), nat(127));    // m_t 172.69 / m_c 1.27

    println!("--- Comparison ---");
    println!("  DRLT chain     = {}", decimal(&chain, 6));
    println!("  1/α_em         = {}  (full-lattice reading)", decimal(&inv_em, 6));
    println!("  PDG m_t/m_c    = {}  (172.69 / 1.27)", decimal(&pdg, 6));

    let d_chain = sub_q(&pdg, &chain);
    let d_em    = sub_q(&pdg, &inv_em);
    let pct = |d: &Q| mul_q(&mul_q(d, &(nat(100), nat(1))), &(pdg.1.clone(), pdg.0.clone()));
    println!("  |Δ| chain      ≈ {} %", decimal(&pct(&d_chain), 3));
    println!("  |Δ| 1/α_em     ≈ {} %", decimal(&pct(&d_em), 3));

    println!("\n→ chain reading wins (0.45 % vs 0.78 %).  m_t/m_c follows");
    println!("  its OWN atomic polynomial: NS·d²·ζ(2) + NS·NT²,");
    println!("  not the 1/α_em polynomial.  The \"double 137\" is");
    println!("  numerical proximity, not structural identity.");
    println!("\nLean cite: QuarkHierarchy.mt_mc_chain_atomic (0-axiom)");
}
