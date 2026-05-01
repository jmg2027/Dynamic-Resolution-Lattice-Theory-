//! 1/α_em(IR) **with** Dyson tail α_GUT/(NS+1) = 1/(100·ζ(2)).
//!
//! Mirrors `lean/E213/Physics/AlphaEMWithTail.lean`.  Bracket form:
//!   inv_lower_with_tail(N) = inv_lower_tight(N) + 1/(100·upper(N))
//!   inv_upper_with_tail(N) = inv_full_upper(N)  + 1/(100·S(N))
//! All ℕ-pair arithmetic.  N ≥ 1 for upper (S(0).num = 0).

use crate::alpha_em::{inv_full_upper, inv_lower_tight};
use crate::basel::{s_partial, upper, Q};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// Lean: `AlphaEMWithTail.inv_lower_with_tail`.
pub fn inv_lower_with_tail(n: u64) -> Q {
    let p = inv_lower_tight(n);
    let u = upper(n);
    let scale = nat(100) * &u.0;
    (&p.0 * &scale + &u.1 * &p.1, &p.1 * &scale)
}

/// Lean: `AlphaEMWithTail.inv_upper_with_tail`.  N ≥ 1.
pub fn inv_upper_with_tail(n: u64) -> Q {
    assert!(n >= 1, "inv_upper_with_tail requires N ≥ 1 (S(0).num = 0)");
    let p = inv_full_upper(n);
    let s = s_partial(n);
    let scale = nat(100) * &s.0;
    (&p.0 * &scale + &s.1 * &p.1, &p.1 * &scale)
}

fn with_tail_contains(n: u64, t_num: u64, t_den: u64) -> bool {
    let lo = inv_lower_with_tail(n);
    let hi = inv_upper_with_tail(n);
    let tn = nat(t_num); let td = nat(t_den);
    &lo.0 * &td < &tn * &lo.1 && &tn * &hi.1 < &hi.0 * &td
}

/// Lean: `AlphaEMWithTail.n20_with_tail_contains_observed` /
/// `n50_with_tail_contains_observed` — observed 137.036 ∈ bracket.
pub fn bracket_137036_with_tail_at(n: u64) -> bool {
    with_tail_contains(n, 137036, 1000)
}

/// Lean: `AlphaEMWithTail.n20_with_tail_contains_candidate` —
/// candidate asymptote 137.0354 ∈ bracket.
pub fn bracket_candidate_with_tail_at(n: u64) -> bool {
    with_tail_contains(n, 1370354, 10000)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: `n20_with_tail_contains_observed`.
    #[test] fn observed_at_20() { assert!(bracket_137036_with_tail_at(20)); }

    /// Lean: `n50_with_tail_contains_observed`.
    #[test] fn observed_at_50() { assert!(bracket_137036_with_tail_at(50)); }

    /// Lean: `n20_with_tail_contains_candidate`.
    #[test] fn candidate_at_20() { assert!(bracket_candidate_with_tail_at(20)); }

    /// At N=200 the with-tail bracket is wide enough that observed
    /// is *still* inside (asymptote ≈ 137.0354 + ζ(2)-bracket residue).
    #[test] fn observed_at_200() { assert!(bracket_137036_with_tail_at(200)); }
}
