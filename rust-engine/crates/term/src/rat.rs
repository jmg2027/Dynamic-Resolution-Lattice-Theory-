//! `Rat` — rational pairs as `(BigUint, BigUint) = (num, den)`.
//!
//! Mirror of `lean/E213/Kernel/Rat.lean`:
//!
//! ```lean
//! def equivQ (p q r s : Term) : Bool := equiv (mul p s) (mul q r)
//! def leQ    (p q r s : Term) : Bool := le_b  (mul p s) (mul q r)
//! ```
//!
//! 213 carries rationals as *unreduced* (num, den) pairs and
//! compares by cross-multiplication.  No `Q.add`, `Q.mul`, `gcd`,
//! `reduce` — Lean has none, so neither do we.
//!
//! Lean citation: `E213.Term.Term.equivQ`, `Term.leQ`.

use num_bigint::BigUint;

/// Rational pair.  Denominator must be > 0; not enforced at the
/// type level — 213 establishes positivity per-construction site.
pub type Q = (BigUint, BigUint);

/// `equivQ (p, q) (r, s) ⇔ p·s = q·r`.
pub fn equiv_q(p: &Q, r: &Q) -> bool {
    let (pn, pd) = p; let (rn, rd) = r;
    pn * rd == pd * rn
}

/// `leQ (p, q) (r, s) ⇔ p·s ≤ q·r`  (q, s > 0).
pub fn le_q(p: &Q, r: &Q) -> bool {
    let (pn, pd) = p; let (rn, rd) = r;
    pn * rd <= pd * rn
}

/// Strict `<` via `leQ` + `¬equivQ`.  Useful for bracket checks.
pub fn lt_q(p: &Q, r: &Q) -> bool {
    let (pn, pd) = p; let (rn, rd) = r;
    pn * rd < pd * rn
}

#[cfg(test)]
mod tests {
    use super::*;
    fn q(n: u32, d: u32) -> Q { (n.into(), d.into()) }

    /// Mirror of `Rat.six_ten_eq_three_five : equivQ 6/10 3/5 = true`.
    #[test] fn six_ten_eq_three_five() {
        assert!(equiv_q(&q(6, 10), &q(3, 5)));
    }

    /// Mirror of `Rat.half_eq_five_ten : equivQ 1/2 5/10 = true`.
    #[test] fn half_eq_five_ten() {
        assert!(equiv_q(&q(1, 2), &q(5, 10)));
    }

    /// Mirror of `Rat.alphaGUT_lt_quarter : leQ 6/25 1/4 = true`.
    #[test] fn alpha_gut_lt_quarter() {
        assert!(lt_q(&q(6, 25), &q(1, 4)));
    }
}
