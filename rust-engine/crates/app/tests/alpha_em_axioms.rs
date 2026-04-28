//! Integration tests — α_em bracket re-execution + certificate.
//!
//! Maps to `lean/E213/Physics/AlphaEM137{,Tight}.lean` and
//! `lean/E213/Tools/CertChecker.lean`.

use drlt_app::alpha_em::{bracket_137_at, inv_full_upper, inv_lower_tight};
use drlt_app::certificate::{Cmp, Step};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// Lean: `bracket_137_in_at_10` (loose).
#[test] fn contains_137_at_10() { assert!(bracket_137_at(10).contains_137); }

/// Lean: `bracket_137_in_at_10_tight` (width ~ 0.55).
#[test] fn contains_137_at_10_tight() {
    let r = bracket_137_at(10);
    assert!(r.contains_137);
    assert_eq!(r.lo, inv_lower_tight(10));
}

/// Lean: `bracket_137_in_at_20_tight` (width ~ 0.14).
#[test] fn contains_137_at_20() { assert!(bracket_137_at(20).contains_137); }

/// Lean: `bracket_138_excluded_at_20`.
#[test] fn excludes_138_at_20() { assert!(bracket_137_at(20).excludes_138); }

/// Lean: `capstone_n20` — contains 137 ∧ excludes 138.
#[test] fn capstone_n20() {
    let r = bracket_137_at(20);
    assert!(r.contains_137 && r.excludes_138);
}

#[test] fn bracket_narrows_with_n() {
    let r10 = bracket_137_at(10);
    let r30 = bracket_137_at(30);
    assert!(r10.contains_137 && r30.contains_137);
}

#[test] fn excludes_136_at_20() {
    let r = bracket_137_at(20);
    let lhs = nat(136) * &r.lo.1;
    assert!(lhs < r.lo.0);
}

#[test] fn certificate_emits_correct_step_count() {
    use drlt_app::certificate::Certificate;
    let mut c = Certificate::new();
    c.push(Step::Cite { lemma: "x".into() });
    c.push(Step::Bound {
        lhs: (nat(1), nat(1)), cmp: Cmp::Lt, rhs: (nat(2), nat(1)),
    });
    assert_eq!(c.steps.len(), 2);
    let json = c.to_json();
    assert!(json.contains("Cite") && json.contains("Bound"));
}

#[test] fn inv_upper_at_20_is_positive() {
    let u = inv_full_upper(20);
    assert!(u.0 > BigUint::from(0u32));
    assert!(u.1 > BigUint::from(0u32));
}
