//! `dark-energy` — Ω_Λ = (1 − 1/π)·(1 + α_GUT/d)
//! Lean: DarkEnergy.lean + Research.Real213CutTrig (leibnizPiPartial).
//!
//! Bare: 1 − c/(2π) = 1 − 1/π ≈ 0.6817 (horizon angular deficit)
//! α_GUT/d correction: ×1.00486 → 0.6850.
//! Observed Planck/DESI: Ω_Λ ≈ 0.685.
//!
//! ★ Fully 213-internal (2026-04-30 refactor): 1/π is no longer a
//! hardcoded rational input.  It is computed from the Leibniz series
//!   π/4 = Σ (−1)^i/(2i+1)
//! via `drlt_app::wallis::pi_bracket(N_pi)` — alternating-series
//! bracket with explicit modulus (width ≤ 2/(2N_pi+1)).  Both ζ(2)
//! (via Basel) and 1/π (via Wallis) are now Lean-cited 213-native
//! brackets — no external transcendental input.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};
use drlt_app::wallis::inv_pi_bracket;

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l >= r { l - r } else { num_bigint::BigUint::from(0u32) };
    (n, &a.1 * &b.1)
}

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let n_pi: u64 = std::env::args().nth(2)
        .and_then(|s| s.parse().ok()).unwrap_or(200);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== Ω_Λ from K_{{3,2}}^{{(2)}} (N_ζ = {n}, N_π = {n_pi}) ===\n");

    // 1/π bracket from Leibniz series — 213-internal, no external input.
    let (inv_pi_lo, inv_pi_hi) = inv_pi_bracket(n_pi);
    println!("1/π bracket  [{}, {}]  (Leibniz n={n_pi})",
        decimal(&inv_pi_lo, 12), decimal(&inv_pi_hi, 12));
    println!("α_GUT        ≈ {}", decimal(&agut, 12));

    let one = (nat(1), nat(1));
    // bare = 1 − 1/π.  Lower 1/π → larger bare; upper 1/π → smaller bare.
    let bare_hi = sub_q(&one, &inv_pi_lo);
    let bare_lo = sub_q(&one, &inv_pi_hi);
    println!("1 − 1/π      ∈ [{}, {}]",
        decimal(&bare_lo, 9), decimal(&bare_hi, 9));

    // (1 + α_GUT/d) = 1 + α_GUT/5  (α_GUT itself is a bracket, but
    // we use the tight value here — refinement deferred).
    let agut_over_d: Q = (agut.0.clone(), &agut.1 * nat(5));
    let corr: Q = (&agut_over_d.0 + &agut_over_d.1, agut_over_d.1.clone());
    println!("(1 + α_GUT/d) ≈ {}", decimal(&corr, 9));

    let omega_lo = mul_q(&bare_lo, &corr);
    let omega_hi = mul_q(&bare_hi, &corr);
    println!();
    println!("DRLT Ω_Λ      ∈ [{}, {}]   ★",
        decimal(&omega_lo, 9), decimal(&omega_hi, 9));
    let observed: Q = (nat(685), nat(1000));
    println!("Observed Ω_Λ  = {}  (Planck/DESI ± 0.007)",
        decimal(&observed, 4));

    // Check: observed in bracket?
    let lo_le = &omega_lo.0 * &observed.1 <= &observed.0 * &omega_lo.1;
    let obs_le_hi = &observed.0 * &omega_hi.1 <= &omega_hi.0 * &observed.1;
    println!("\nbracket contains observed: {}",
        if lo_le && obs_le_hi { "YES ★" } else { "NO" });

    println!("\nLean cites: DarkEnergy + Research.Real213CutTrig.leibnizPiPartial");
}

