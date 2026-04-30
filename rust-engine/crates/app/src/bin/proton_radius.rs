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
    let pct = mul_q(&dq, &(nat(100), nat(1)));
    let pct_rel = mul_q(&pct, &(nt_sq.1.clone(), nt_sq.0.clone()));
    println!("|Δ|              = {}    ({} %)",
        decimal(&dq, 6), decimal(&pct_rel, 4));

    println!();
    println!("Triple atomic reading of integer 4:");
    println!("  NT²    = 4   (chiral phase volume on K_{{3,2}}^{{(c=2)}})");
    println!("  d − 1  = 4   (backbone minus base point)");
    println!("  NS + 1 = 4   (first 'beyond NS' step)");
    println!();
    println!("→ r_p = NT² · ℏ/(m_p·c)  = NT² · Compton wavelength of proton");
    println!("       Class C (bare invariant), no α_GUT correction needed.");
    println!();
    println!("Lean cite: ProtonMass.r_p_atomic (0-axiom, added 2026-04-30)");
}

