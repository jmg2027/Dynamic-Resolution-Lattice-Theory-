//! Integration tests — `Term` axioms and Lean lemma mirrors.
//!
//! Each test names the Lean source it mirrors so a reviewer can map
//! `lean/E213/Kernel/Term.lean` ↔ Rust 1:1.

use drlt_term::term::{c, d, n_s, n_t, Term};
use num_bigint::BigUint;

// ── Constants (mirror Lean Term.nS / nT / d / c) ──────────────────

#[test] fn const_n_s_is_3() { assert_eq!(n_s().eval(), BigUint::from(3u32)); }
#[test] fn const_n_t_is_2() { assert_eq!(n_t().eval(), BigUint::from(2u32)); }
#[test] fn const_d_is_5()   { assert_eq!(d().eval(),   BigUint::from(5u32)); }
#[test] fn const_c_is_2()   { assert_eq!(c().eval(),   BigUint::from(2u32)); }

// ── Eval axioms (Lean `Term.eval` structural cases) ───────────────

#[test] fn eval_zero_is_0() { assert_eq!(Term::Zero.eval(), BigUint::from(0u32)); }

#[test] fn eval_succ_adds_one() {
    assert_eq!(Term::succ(n_s()).eval(), BigUint::from(4u32));
}

#[test] fn eval_add_is_plus() {
    assert_eq!(Term::add(n_s(), n_t()).eval(), BigUint::from(5u32));
}

#[test] fn eval_mul_is_times() {
    assert_eq!(Term::mul(d(), d()).eval(), BigUint::from(25u32));
}

// ── equiv: reflexive, symmetric, transitive ───────────────────────

#[test] fn equiv_reflexive() {
    let t = Term::add(n_s(), n_t());
    assert!(Term::equiv(&t, &t));
}

#[test] fn equiv_symmetric() {
    let a = Term::add(n_s(), n_t());
    let b = Term::add(n_t(), n_s());
    assert!(Term::equiv(&a, &b) && Term::equiv(&b, &a));
}

#[test] fn equiv_transitive() {
    let a = Term::add(n_s(), n_t());                    // 5
    let b = d();                                        // 5
    let c = Term::succ(Term::add(n_t(), n_t()));        // 1+(2+2) = 5
    assert!(Term::equiv(&a, &b) && Term::equiv(&b, &c));
    assert!(Term::equiv(&a, &c));
}

// ── Negative: equiv detects difference ────────────────────────────

#[test] fn equiv_distinguishes_3_vs_5() {
    assert!(!Term::equiv(&n_s(), &d()));
}

// ── Algebra fact mirrors ──────────────────────────────────────────

/// `2·n_S² = 18` (input to `Compare.dsq_ge_2nSsq`).
#[test] fn two_n_s_squared_is_18() {
    let t = Term::mul(Term::from_nat(2), Term::mul(n_s(), n_s()));
    assert_eq!(t.eval(), BigUint::from(18u32));
}

/// `d³ = 125`  (input to `Compare.two_nS_cube_le_d_cube`).
#[test] fn d_cubed_is_125() {
    let t = Term::mul(d(), Term::mul(d(), d()));
    assert_eq!(t.eval(), BigUint::from(125u32));
}
