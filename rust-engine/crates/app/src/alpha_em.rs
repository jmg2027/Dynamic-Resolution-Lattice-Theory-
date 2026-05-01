//! 1/α_em(IR) candidate brackets.
//!
//! Mirrors `Physics.AlphaEM137{,Tight}` and `AlphaEMGap`.  All
//! formulas as ℕ-pair (num, den) inlined — no Q-algebra type.

use crate::basel::{s_partial, upper, Q};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// Lean: `inv_full_lower N = (180·s.1 + 115·s.2, 3·s.2)`.
pub fn inv_full_lower(n: u64) -> Q {
    let s = s_partial(n);
    (&s.0 * 180u32 + &s.1 * 115u32, &s.1 * 3u32)
}

/// Lean: `inv_full_upper N = (180·u.1 + 115·u.2, 3·u.2)` (u = upper N).
pub fn inv_full_upper(n: u64) -> Q {
    let u = upper(n);
    (&u.0 * 180u32 + &u.1 * 115u32, &u.1 * 3u32)
}

/// Lean: `inv_lower_tight N` — telescopes by `+1/(N+1)`.
pub fn inv_lower_tight(n: u64) -> Q {
    let s = s_partial(n);
    let n_p1 = nat(n + 1);
    let lhs_num = &s.0 * 180u32 * &n_p1
        + &s.1 * (nat(180) + nat(115) * &n_p1);
    (lhs_num, nat(3) * &s.1 * &n_p1)
}

/// `bracket_137_at(N)`: lo<137 ∧ 137<hi (contains_137);
/// hi<138 (excludes_138, sharpness from above).
pub fn bracket_137_at(n: u64) -> BracketResult {
    let lo = inv_lower_tight(n);
    let hi = inv_full_upper(n);
    let v137 = nat(137); let v138 = nat(138);
    let contains_137 = lo.0 < &v137 * &lo.1 && &v137 * &hi.1 < hi.0;
    let excludes_138 = &hi.0 < &(&v138 * &hi.1);
    BracketResult { lo, hi, contains_137, excludes_138 }
}

/// Does the bracket at N contain `t_num/t_den`?
fn bracket_contains_at(n: u64, t_num: u64, t_den: u64) -> bool {
    let lo = inv_lower_tight(n);
    let hi = inv_full_upper(n);
    let tn = nat(t_num); let td = nat(t_den);
    &lo.0 * &td < &tn * &lo.1 && &tn * &hi.1 < &hi.0 * &td
}

/// Lean: `AlphaEMGap.n50_bracket_contains_observed`.
/// observed `137.036 = (137036, 1000)` ∈ bracket at N.
pub fn bracket_137036_at(n: u64) -> bool {
    bracket_contains_at(n, 137036, 1000)
}

/// Lean: `AlphaEMGap.n50_bracket_contains_candidate`.
/// candidate `137.0354 = (1370354, 10000)` ∈ bracket at N.
pub fn bracket_candidate_at(n: u64) -> bool {
    bracket_contains_at(n, 1370354, 10000)
}

#[derive(Clone, Debug)]
pub struct BracketResult {
    pub lo: Q,
    pub hi: Q,
    pub contains_137: bool,
    pub excludes_138: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn contains_137_at_10() { assert!(bracket_137_at(10).contains_137); }
    #[test] fn contains_137_at_20() { assert!(bracket_137_at(20).contains_137); }
    #[test] fn excludes_138_at_20() { assert!(bracket_137_at(20).excludes_138); }
}
