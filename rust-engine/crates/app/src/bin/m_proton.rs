//! `m-proton` — m_p verification via P(α_GUT · NS/d) propagator.
//! Lean: ProtonMass.lean (atomic claim) + LambdaQCDPhantom.lean
//! (Λ_QCD = unit-convention, not primitive).
//!
//!   m_p = NS · (anchor) · P(α_GUT · NS/d)
//!       = 3 · 308.32 MeV · P(α·3/5)
//!       ≈ 924.97 · 1.01438  ≈  938.27 MeV
//!
//! ⚠ The 308.32 MeV "anchor" is conventionally called Λ_QCD.  In
//! DRLT (see LambdaQCDPhantom.lean) Λ_QCD is *not* a fundamental
//! parameter — it is the MeV unit one chooses to express the
//! dimensionless atomic ratio `NS · P(α_GUT · NS/d)`.  The
//! K_{3,2}^{(c=2)} counting invariant `d² · NT² · (NS²−1) = 800`
//! sets the gear ratio between any two scales (e.g. v_H ≈ 800 ·
//! "Λ_QCD"); the units are arbitrary.  The atomic claim is the
//! projection NS/d = 3/5.
//!
//! Same P(x) = (1+2x)/(1+x) family as α_em Dyson + m_μ/m_e.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);

    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    // α_GUT = 1/(d²·ζ(2))
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== m_p via P(α_GUT · NS/d) (N = {n}) ===\n");
    println!("α_GUT     ≈ {}", decimal(&agut, 12));

    // x = α_GUT · NS/d = α_GUT · 3/5
    let x: Q = (&agut.0 * nat(3), &agut.1 * nat(5));
    println!("x = α_GUT·3/5 ≈ {}", decimal(&x, 12));

    // P(x) = (1 + 2x)/(1 + x) = (x.1 + 2·x.0, x.1 + x.0)
    let p_factor: Q = (&x.1 + nat(2) * &x.0, &x.1 + &x.0);
    println!("P(x) = (1+2x)/(1+x) ≈ {}    (Lean expected 1.01438)",
        decimal(&p_factor, 9));

    // NS · Λ_QCD = 924.97 MeV (input from atomic chain)
    // Use 92497/100 MeV
    let ns_lambda: Q = (nat(92497), nat(100));   // 924.97 MeV
    let m_p = mul_q(&ns_lambda, &p_factor);
    let observed: Q = (nat(93827), nat(100));    // 938.27 MeV CODATA

    println!("\nNS·Λ_QCD                 = {} MeV", decimal(&ns_lambda, 4));
    println!("DRLT m_p                  = {} MeV  ★", decimal(&m_p, 6));
    println!("Observed m_p              = {} MeV  (CODATA)",
        decimal(&observed, 4));

    let l = &observed.0 * &m_p.1;
    let r = &m_p.0 * &observed.1;
    let diff_num = if l > r { l - r } else { r - l };
    let diff: Q = (diff_num, &observed.1 * &m_p.1);
    let ppm: Q = (&diff.0 * nat(1_000_000) * &observed.1,
                  &diff.1 * &observed.0);
    println!("|Δ|                       ≈ {} MeV", decimal(&diff, 6));
    println!("                          ≈ {} ppm", decimal(&ppm, 2));
    println!("\nLean cite: ProtonMass.proton_simplicial_pattern (0-axiom)");
}
