//! Basel partial sum + telescoping upper bound.
//!
//! Mirror of `lean/E213/Physics/BaselBound.lean`.  All ℕ-pair
//! arithmetic, no Q-algebra abstraction — ratios stay as
//! `(BigUint, BigUint)` and compare via cross-multiplication.

use num_bigint::BigUint;

/// Rational pair `(num, den)` matching Lean's `(Nat × Nat)`.
pub type Q = (BigUint, BigUint);

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// `S(0) = 0/1`; `S(n+1) = S(n) + 1/(n+1)²` inlined as ℕ ops:
///   `(p.1·k + p.2, p.2·k)` where `k = (n+1)²`.
/// Lean: `Physics.Basel.S`.
pub fn s_partial(n: u64) -> Q {
    if n == 0 { return (nat(0), nat(1)); }
    let p = s_partial(n - 1);
    let k = nat(n) * nat(n);
    (&p.0 * &k + &p.1, &p.1 * &k)
}

/// `upper(N) = S(N) + 1/N` (telescoping bound for ζ(2)).
/// `upper(0) = 2/1` (placeholder per Lean).
/// Lean: `Physics.Basel.upper`.
pub fn upper(n: u64) -> Q {
    if n == 0 { return (nat(2), nat(1)); }
    let p = s_partial(n);
    let n_q = nat(n);
    (&p.0 * &n_q + &p.1, &p.1 * &n_q)
}

/// Cross-mul `<` on rationals.  Lean: `Physics.Basel.lt`.
pub fn lt_q(p: &Q, q: &Q) -> bool { &p.0 * &q.1 < &q.0 * &p.1 }

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: `S_0 : S 0 = (0, 1)`.
    #[test] fn s0_is_zero() { assert_eq!(s_partial(0), (nat(0), nat(1))); }

    /// Lean: `S_1 : S 1 = (1, 1)`.
    #[test] fn s1_is_one() { assert_eq!(s_partial(1), (nat(1), nat(1))); }

    /// Lean: `S_2 : S 2 = (5, 4)`.
    #[test] fn s2_is_five_quarters() { assert_eq!(s_partial(2), (nat(5), nat(4))); }

    /// Lean: `S_3 : S 3 = (49, 36)`.
    #[test] fn s3_is_49_36() { assert_eq!(s_partial(3), (nat(49), nat(36))); }

    /// Lean: `upper_2 : upper 2 = (14, 8)`.
    #[test] fn upper_2() { assert_eq!(upper(2), (nat(14), nat(8))); }

    /// Lean: `upper_3 : upper 3 = (183, 108)`.
    #[test] fn upper_3() { assert_eq!(upper(3), (nat(183), nat(108))); }

    /// Lean: `bracket_2 : lt (S 2) (upper 2)`.
    #[test] fn bracket_2() { assert!(lt_q(&s_partial(2), &upper(2))); }

    /// Lean: `bracket_3 : lt (S 3) (upper 3)`.
    #[test] fn bracket_3() { assert!(lt_q(&s_partial(3), &upper(3))); }
}
