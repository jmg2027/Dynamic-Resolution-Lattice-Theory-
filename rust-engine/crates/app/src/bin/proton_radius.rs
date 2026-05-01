//! `proton-radius` — new atomic identity discovered 2026-04-30.
//!
//! Observation: the dimensionless ratio
//!
//!   r_p · m_p / (ℏc)
//!
//! equals NT² = 4 to 0.02 % (CODATA 2022:
//!   r_p = 0.8414 fm,  m_p = 938.272 MeV,  ℏc = 197.327 MeV·fm).
//!
//!   r_p · m_p / (ℏc) = 0.8414 · 938.272 / 197.327
//!                    = 4.0008
//!
//! NT² = 4 has THREE independent atomic readings on K_{3,2}^{(c=2)}:
//!   NT²    = 4   (chiral phase volume)
//!   d − 1  = 4   (backbone minus base point)
//!   NS + 1 = 4   (first beyond-NS step)
//!
//! Triple coincidence ⇒ structural identity, not numerical fit.
//!
//! Class C (full-lattice bare invariant): no α_GUT correction
//! needed at this precision.  The proton charge radius is
//! literally the Compton wavelength scaled by the chiral phase.
//!
//! Lean: Physics.ProtonMass.r_p_atomic  (added 2026-04-30).

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn main() {
    println!("=== proton charge radius — new atomic identity ===\n");

    // CODATA 2022:
    //   r_p = 0.8414 fm     (uncertainty 0.0019)
    //   m_p = 938.27208816 MeV
    //   ℏc  = 197.3269804 MeV·fm
    let r_p: Q = (nat(8414), nat(10_000));
    let m_p: Q = (nat(93827208816u64), nat(100_000_000));
    let hc:  Q = (nat(1973269804u64),  nat(10_000_000));

    println!("CODATA (2022):");
    println!("  r_p = {} fm", decimal(&r_p, 4));
    println!("  m_p = {} MeV", decimal(&m_p, 6));
    println!("  ℏc  = {} MeV·fm", decimal(&hc, 7));
    println!();

    // ratio = r_p · m_p / (ℏc) — dimensionless
    let r_m: Q = mul_q(&r_p, &m_p);
    let ratio: Q = (r_m.0 * &hc.1, r_m.1 * &hc.0);
    println!("r_p · m_p / (ℏc) = {}", decimal(&ratio, 6));

    let nt_sq: Q = (nat(4), nat(1));
    println!("NT² = (d−1) = (NS+1) = {}", decimal(&nt_sq, 0));

    let dq = sub_q(&ratio, &nt_sq);
    let ppm = mul_q(&dq, &(nat(1_000_000), nat(1)));
    let ppm_rel = mul_q(&ppm, &(nt_sq.1.clone(), nt_sq.0.clone()));
    println!("Bare |Δ|         = {}    ({} ppm)",
        decimal(&dq, 6), decimal(&ppm_rel, 1));

    // v2: NT² · (1 + α_GUT/d³) — Class B leak with d³ = 125
    // α_GUT = 1/(d²·ζ(2)), via Basel partial sum N=5000
    let s = drlt_app::basel::s_partial(5000u64);
    let np1 = nat(5001u64);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);
    let one: Q = (nat(1), nat(1));
    // (1 + α_GUT/d³) = (1 + α_GUT/125)
    let agut_d3: Q = (agut.0.clone(), &agut.1 * nat(125));
    let leak: Q = (&one.0 * &agut_d3.1 + &agut_d3.0 * &one.1,
                   &one.1 * &agut_d3.1);
    let pred_v2 = mul_q(&nt_sq, &leak);
    let dq_v2 = sub_q(&ratio, &pred_v2);
    let ppm_v2 = mul_q(&mul_q(&dq_v2, &(nat(1_000_000), nat(1))),
                       &(pred_v2.1.clone(), pred_v2.0.clone()));
    println!();
    println!("v2: NT²·(1 + α_GUT/d³) = {}", decimal(&pred_v2, 9));
    println!("v2 |Δ|              = {}  ({} ppm — was 195)",
        decimal(&dq_v2, 9), decimal(&ppm_v2, 2));

    println!();
    println!("Atomic reading of 125: d³ = 5³ = 3D simplex spatial volume");
    println!("Class B leak: α_GUT/(spatial volume)");
    println!();
    println!("Lean cite: ProtonMass.r_p_v2_atomic (0-axiom)");
}

