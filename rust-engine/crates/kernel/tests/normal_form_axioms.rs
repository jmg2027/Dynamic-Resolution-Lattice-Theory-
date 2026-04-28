//! Integration tests — NormalForm: monomial reduction + 5 rule
//! validations + axiom-violation guard.
//!
//! Lean source: `lean/E213/Kernel/MonomialAxioms.lean`.

use drlt_kernel::normal_form::*;
use drlt_kernel::normal_form::rules::*;
use num_bigint::BigUint;

// ── normalize: structural reduction ───────────────────────────────

#[test] fn normalize_const_is_const() {
    let e = Expr::Const(BigUint::from(7u32));
    assert_eq!(normalize(&e), Monomial::from_const(BigUint::from(7u32)));
}

#[test] fn normalize_x_is_x() {
    assert_eq!(normalize(&Expr::X), Monomial::x());
}

#[test] fn normalize_x_times_y() {
    let e = Expr::Mul(Box::new(Expr::X), Box::new(Expr::Y));
    let m = normalize(&e);
    assert_eq!((m.x_pow, m.y_pow), (1, 1));
    assert_eq!(m.coeff, BigUint::from(1u32));
}

#[test] fn normalize_x_squared() {
    let m = normalize(&Expr::Pow(Box::new(Expr::X), 2));
    assert_eq!((m.x_pow, m.y_pow), (2, 0));
}

#[test] fn normalize_const_times_x_squared() {
    let e = Expr::Mul(
        Box::new(Expr::Const(BigUint::from(3u32))),
        Box::new(Expr::Pow(Box::new(Expr::X), 2)),
    );
    let m = normalize(&e);
    assert_eq!((m.coeff, m.x_pow, m.y_pow), (BigUint::from(3u32), 2, 0));
}

// ── 5 starter rules — Lean lemma mirrors ──────────────────────────

#[test] fn rule_ns_mul_nt_eq_six() { assert!(NsMulNtEqSix::validate()); }
#[test] fn rule_mul_comm_ns_nt()   { assert!(MulCommNsNt::validate()); }
#[test] fn rule_ns_sq_eq_9()       { assert!(NsSqEq9::validate()); }
#[test] fn rule_nt_sq_eq_4()       { assert!(NtSqEq4::validate()); }
#[test] fn rule_d_sq_eq_25()       { assert!(DSqEq25::validate()); }

// ── Citation strings present ──────────────────────────────────────

#[test] fn citations_named_correctly() {
    assert!(NsMulNtEqSix::LEAN_THM.ends_with("ns_mul_nt_eq_six"));
    assert!(MulCommNsNt::LEAN_THM.ends_with("mul_comm_ns_nt"));
    assert!(DSqEq25::LEAN_THM.ends_with("d_sq_eq_25"));
}

// ── Axiom violation guard: wrong identity rejected ────────────────

#[test] fn negative_wrong_identity_rejected() {
    struct Wrong;
    impl RewriteRule for Wrong {
        const LEAN_THM: &'static str = "fake";
        fn lhs() -> Expr { Expr::Mul(Box::new(Expr::X), Box::new(Expr::Y)) }
        fn rhs() -> Expr { Expr::Const(BigUint::from(7u32)) }   // 7 ≠ 6
    }
    assert!(!Wrong::validate());
}

#[test] fn negative_x_squared_neq_8() {
    struct Wrong;
    impl RewriteRule for Wrong {
        const LEAN_THM: &'static str = "fake";
        fn lhs() -> Expr { Expr::Pow(Box::new(Expr::X), 2) }    // = 9
        fn rhs() -> Expr { Expr::Const(BigUint::from(8u32)) }   // 8 ≠ 9
    }
    assert!(!Wrong::validate());
}
