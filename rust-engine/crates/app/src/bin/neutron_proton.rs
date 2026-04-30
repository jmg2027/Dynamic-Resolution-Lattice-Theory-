//! `neutron-proton` — Δm_np with S(2)/ζ(2) EM-excess fraction.
//! Lean: NeutronProton.lean.
//!
//!   Δm_np = (m_d − m_u) · (1 − S(2)/ζ(2)) · 12
//!         where 12 = c·NS·NT (directed bipartite edges)
//!         S(2) = 5/4, ζ(2) = π²/6
//!         (1 − S(2)/ζ(2)) = EM-excess long-range fraction
//!
//! (m_d − m_u) ≈ 2.7 MeV (input from quark mass chain).

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l >= r { l - r } else { num_bigint::BigUint::from(0u32) };
    (n, &a.1 * &b.1)
}

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    println!("=== Δm_np = m_n − m_p (Lean NeutronProton) ===\n");
    let s2: Q = (nat(5), nat(4));    // S(2) = 1 + 1/4 = 5/4
    println!("S(2)              = {}", decimal(&s2, 6));
    println!("ζ(2)              ≈ {}", decimal(&zeta_tight, 9));

    // S(2)/ζ(2) cross-mul: (s2.0·zeta.1, s2.1·zeta.0)
    let s2_over_zeta: Q = (&s2.0 * &zeta_tight.1, &s2.1 * &zeta_tight.0);
    println!("S(2)/ζ(2)         ≈ {}", decimal(&s2_over_zeta, 9));

    let one = (nat(1), nat(1));
    let frac = sub_q(&one, &s2_over_zeta);  // 1 − S(2)/ζ(2)
    println!("1 − S(2)/ζ(2)     ≈ {}    (EM-excess fraction)",
        decimal(&frac, 9));

    // Δm_np = (m_d − m_u) · frac · 12
    // Input m_d − m_u ≈ 2.7 MeV (CODATA-ish input)
    let dm_quark: Q = (nat(27), nat(10));     // 2.7 MeV
    let twelve: Q = (nat(12), nat(1));
    let delta = mul_q(&mul_q(&dm_quark, &frac), &twelve);

    println!();
    println!("(m_d − m_u)       = {} MeV (input)", decimal(&dm_quark, 2));
    println!("12 = c·NS·NT      = 12  (directed edges)");
    println!("Naive product     = {} MeV", decimal(&delta, 6));
    let observed: Q = (nat(12933), nat(10000));    // 1.2933 MeV CODATA
    println!("Observed Δm_np    = {} MeV  (CODATA)",
        decimal(&observed, 6));
    println!();
    println!("NOTE: Lean NeutronProton.lean is honest: this naive");
    println!("  product is incomplete (SM_022 / HadronMasses adds");
    println!("  EM-QCD compensation).  Atomic *primitives* exhibited:");
    println!("    12 = c·NS·NT (directed bipartite edges)");
    println!("    S(2)/ζ(2) = 5/(4·π²/6) (long-range vs leading)");

    println!("\n★ '12' = c·NS·NT (directed edges) appears in:");
    println!("  Δm_np, 1/α_2 prefactor, photon kernel edge count");
    println!("\nLean cite: NeutronProton (uses S(2)/ζ(2), 12=c·NS·NT)");
}
