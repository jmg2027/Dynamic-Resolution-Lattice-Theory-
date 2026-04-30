//! `massless-particles` — DRLT identification of massless force carriers.
//! Lean: MasslessParticles.lean.
//!
//! Massless ↔ N_eff = ∞ (no rank exhaustion of Gram).
//! Massive  ↔ N_eff = finite (Gram saturates at NT-th hop).
//!
//!   Photon  γ : N_eff = ∞ (cross-sector U(1))  → massless ✓
//!   Gluon   g : N_eff = 1 (AAA confined)        → asymptotically massless
//!   W, Z      : N_eff = NT (rank exhaustion)    → massive
//!
//! ★ Photon kernel cycle space dim = b_1 = NS² − 1 = 8 = 1/α_3.

fn main() {
    println!("=== Massless particles via Gram rank ===\n");
    println!("DRLT criterion: massless ↔ N_eff = ∞");
    println!("                 massive  ↔ N_eff = finite (rank exhaustion)\n");

    println!("─────────────────────────────────────────────────────────");
    println!("  Particle    Sector        N_eff         Mass status");
    println!("─────────────────────────────────────────────────────────");
    println!("  γ (photon)  Cross         ∞ (no exh.)   MASSLESS ✓");
    println!("  g (gluon)   AAA confined  1 (C(NS,NS))  MASSLESS asympt.");
    println!("  W, Z        ABB temporal  NT = 2        MASSIVE ✓");
    println!("  Higgs h     AABB self-dual…             125 GeV (m_H)");
    println!("  graviton    G modulus     trace mode    MASSLESS");

    println!("\n--- Why W/Z are massive (★ structural) ---");
    println!("  α_2 N_eff = NT = 2 → Gram exhausts at 2nd hop");
    println!("  → cannot couple beyond 2nd-order → propagator finite");
    println!("  → finite mass.  m_W² ∝ 1/N_eff² + ...");
    println!();
    println!("  α_3 N_eff = 1 (single AAA hinge): confinement.");
    println!("  α_em N_eff = ∞: no exhaustion → photon massless.");

    println!("\n--- Photon kernel = b_1(K_{{3,2}}^{{(2)}}) = 8 ---");
    println!("  Photon mode count = cycle space dim = E − V + 1");
    println!("                   = 12 − 5 + 1 = 8 = NS² − 1 = 1/α_3");
    println!("  ★ Same integer 8: photon mode count = strong coupling.");

    println!("\nLean cite: MasslessParticles.three_force_mass_pattern (0-axiom)");
}
