//! 1/α_em(IR) candidate brackets.
//!
//! Mirrors:
//!   * `Physics.AlphaEM137.inv_full_lower / inv_full_upper`
//!   * `Physics.AlphaEM137Tight.inv_lower_tight / inv_upper`
//! Plus `bracket_137_in_at_*_tight` end-points.
//!
//! All formulas as ℕ-pair (num, den) inlined — no Q-algebra type.

use crate::basel::{s_partial, upper, Q};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// Lean: `inv_full_lower N = (180·s.1 + 115·s.2, 3·s.2)` where `s = S N`.
pub fn inv_full_lower(n: u64) -> Q {
    let s = s_partial(n);
    (&s.0 * 180u32 + &s.1 * 115u32, &s.1 * 3u32)
}

/// Lean: `inv_full_upper N = (180·u.1 + 115·u.2, 3·u.2)` where `u = upper N`.
pub fn inv_full_upper(n: u64) -> Q {
    let u = upper(n);
    (&u.0 * 180u32 + &u.1 * 115u32, &u.1 * 3u32)
}

/// Lean: `inv_lower_tight N = (180·s.1·(N+1) + s.2·(180 + 115·(N+1)),
///                              3·s.2·(N+1))`
/// where `s = S N`.  Tight version (telescoping by `+1/(N+1)`).
pub fn inv_lower_tight(n: u64) -> Q {
    let s = s_partial(n);
    let n_p1 = nat(n + 1);
    let lhs_num = &s.0 * 180u32 * &n_p1
        + &s.1 * (nat(180) + nat(115) * &n_p1);
    let lhs_den = nat(3) * &s.1 * &n_p1;
    (lhs_num, lhs_den)
}

/// `bracket_137_at(N) = (lo, hi, contains_137, excludes_138)`.
///   contains_137 iff lo.1 < 137·lo.2 ∧ 137·hi.2 < hi.1
///   excludes_138 iff hi.1 < 138·hi.2  (sharpness from above)
pub fn bracket_137_at(n: u64) -> BracketResult {
    let lo = inv_lower_tight(n);
    let hi = inv_full_upper(n);
    let v137 = nat(137);
    let v138 = nat(138);
    let contains_137 = lo.0 < &v137 * &lo.1 && &v137 * &hi.1 < hi.0;
    let excludes_138 = &hi.0 < &(&v138 * &hi.1);
    BracketResult { lo, hi, contains_137, excludes_138 }
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

    /// Lean: `bracket_137_in_at_10_tight` (width ~ 0.55).
    #[test] fn contains_137_at_10() { assert!(bracket_137_at(10).contains_137); }

    /// Lean: `bracket_137_in_at_20_tight` (width ~ 0.14).
    #[test] fn contains_137_at_20() { assert!(bracket_137_at(20).contains_137); }

    /// Lean: `bracket_138_excluded_at_20`.
    #[test] fn excludes_138_at_20() { assert!(bracket_137_at(20).excludes_138); }
}
