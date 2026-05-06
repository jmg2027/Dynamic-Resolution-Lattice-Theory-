//! Integration tests — `Rat` (cross-mul) Lean mirrors + axioms.
//!
//! 1:1 with `lean/E213/Kernel/Rat.lean`.  No `Q.add` / `Q.mul` —
//! Lean has none, so neither do we.  All comparisons via cross-mul.

use drlt_term::rat::{equiv_q, le_q, lt_q, Q};
use num_bigint::BigUint;

fn q(n: u32, d: u32) -> Q { (BigUint::from(n), BigUint::from(d)) }

// ── Direct lemma mirrors (Lean `theorem ... := rfl`) ──────────────

/// Lean: `Rat.six_ten_eq_three_five : equivQ 6/10 3/5 = true`.
#[test] fn six_ten_eq_three_five()  { assert!(equiv_q(&q(6, 10), &q(3, 5))); }

/// Lean: `Rat.half_eq_five_ten : equivQ 1/2 5/10 = true`.
#[test] fn half_eq_five_ten()       { assert!(equiv_q(&q(1, 2), &q(5, 10))); }

/// Lean: `Rat.alphaGUT_base : equivQ 6/25 6/25 = true`.
#[test] fn alpha_gut_base()         { assert!(equiv_q(&q(6, 25), &q(6, 25))); }

/// Lean: `Rat.dsq_over_four_irred : equivQ 25/4 25/4 = true`.
#[test] fn dsq_over_four_irred()    { assert!(equiv_q(&q(25, 4), &q(25, 4))); }

/// Lean: `Rat.alphaGUT_lt_quarter : leQ 6/25 1/4 = true`.
#[test] fn alpha_gut_lt_quarter()   { assert!(lt_q(&q(6, 25), &q(1, 4))); }

// ── equivQ: reflexive, symmetric, transitive ──────────────────────

#[test] fn equiv_q_reflexive()  { assert!(equiv_q(&q(7, 13), &q(7, 13))); }

#[test] fn equiv_q_symmetric() {
    assert!(equiv_q(&q(6, 10), &q(3, 5)));
    assert!(equiv_q(&q(3, 5),  &q(6, 10)));
}

#[test] fn equiv_q_transitive() {
    assert!(equiv_q(&q(2, 4), &q(1, 2)));
    assert!(equiv_q(&q(1, 2), &q(5, 10)));
    assert!(equiv_q(&q(2, 4), &q(5, 10)));
}

// ── leQ axioms ────────────────────────────────────────────────────

#[test] fn le_q_reflexive()     { assert!(le_q(&q(3, 7), &q(3, 7))); }
#[test] fn lt_q_irreflexive()   { assert!(!lt_q(&q(3, 7), &q(3, 7))); }

#[test] fn le_q_transitive() {
    assert!(le_q(&q(1, 4), &q(1, 3)));
    assert!(le_q(&q(1, 3), &q(1, 2)));
    assert!(le_q(&q(1, 4), &q(1, 2)));
}

#[test] fn lt_q_asymmetric() {
    assert!(lt_q(&q(6, 25), &q(1, 4)));
    assert!(!lt_q(&q(1, 4), &q(6, 25)));
}

// ── Negative: rejection of distinct rationals ─────────────────────

#[test] fn equiv_q_rejects_3_5_vs_2_5() { assert!(!equiv_q(&q(3, 5), &q(2, 5))); }
#[test] fn equiv_q_rejects_2_3_vs_3_2() { assert!(!equiv_q(&q(2, 3), &q(3, 2))); }

// ── Unreduced form: equivQ does not require reduction ─────────────

/// 213 carries unreduced (num, den) — equivQ tolerates any scaling.
/// This guards against accidental gcd/reduce slipping in.
#[test] fn equiv_q_tolerates_unreduced() {
    assert!(equiv_q(&q(2, 4),  &q(1,  2)));
    assert!(equiv_q(&q(50, 100), &q(1, 2)));
    assert!(equiv_q(&q(0, 7),  &q(0, 11)));   // 0 representations
}
