//! Integration tests — `Compare` Lean lemma mirrors + axioms.
//!
//! 1:1 with `lean/E213/Kernel/Compare.lean`, each closed by `rfl`
//! there; here closed by `assert!(le_b(..) || lt_b(..))`.

use drlt_term::compare::{le_b, lt_b};
use drlt_term::term::{c, d, n_s, n_t, Term};

// ── Direct lemma mirrors (Lean `theorem ... := rfl`) ──────────────

/// Lean: `Compare.nT_lt_nS : lt_b nT nS = true`.
#[test] fn nt_lt_ns()    { assert!(lt_b(&n_t(), &n_s())); }

/// Lean: `Compare.nS_lt_d  : lt_b nS d  = true`.
#[test] fn ns_lt_d()     { assert!(lt_b(&n_s(), &d())); }

/// Lean: `Compare.nT_le_c : le_b nT c = true`.
#[test] fn nt_le_c()     { assert!(le_b(&n_t(), &c())); }

/// Lean: `Compare.dsq_ge_2nSsq : le_b (2·n_S²) (d²) = true` (18 ≤ 25).
#[test] fn dsq_ge_2_n_s_sq() {
    let two_ns_sq = Term::mul(Term::from_nat(2), Term::mul(n_s(), n_s()));
    let dsq       = Term::mul(d(), d());
    assert!(le_b(&two_ns_sq, &dsq));
}

/// Lean: `Compare.two_nS_cube_le_d_cube : 2·n_S³ ≤ d³` (54 ≤ 125).
#[test] fn two_n_s_cube_le_d_cube() {
    let lhs = Term::mul(Term::from_nat(2), Term::mul(n_s(), Term::mul(n_s(), n_s())));
    let rhs = Term::mul(d(), Term::mul(d(), d()));
    assert!(le_b(&lhs, &rhs));
}

/// Lean: `two_nS_sq_lt_d_sq_plus_1 : 2·n_S² < d² + 1` (18 < 26).
#[test] fn two_n_s_sq_lt_d_sq_plus_1() {
    let lhs = Term::mul(Term::from_nat(2), Term::mul(n_s(), n_s()));
    let rhs = Term::add(Term::mul(d(), d()), Term::succ(Term::Zero));
    assert!(lt_b(&lhs, &rhs));
}

// ── Axioms of order ───────────────────────────────────────────────

#[test] fn le_b_reflexive()      { assert!(le_b(&d(), &d())); }
#[test] fn lt_b_irreflexive()    { assert!(!lt_b(&d(), &d())); }

#[test] fn le_b_transitive() {
    assert!(le_b(&n_t(), &n_s()) && le_b(&n_s(), &d()));
    assert!(le_b(&n_t(), &d()));
}

#[test] fn lt_b_transitive() {
    assert!(lt_b(&n_t(), &n_s()) && lt_b(&n_s(), &d()));
    assert!(lt_b(&n_t(), &d()));
}

#[test] fn lt_b_implies_le_b() {
    assert!(lt_b(&n_t(), &n_s()));
    assert!(le_b(&n_t(), &n_s()));
}

// ── Negative / axiom-violation guards ─────────────────────────────

/// `lt_b a b` and `lt_b b a` cannot both hold (asymmetry).
#[test] fn lt_b_asymmetric() {
    assert!(lt_b(&n_t(), &n_s()));
    assert!(!lt_b(&n_s(), &n_t()));
}

/// `le_b a b ∧ le_b b a → equiv a b` (antisymmetry).
#[test] fn le_b_antisymmetric_for_distinct() {
    assert!(le_b(&n_t(), &c()));   // 2 ≤ 2
    assert!(le_b(&c(), &n_t()));   // 2 ≤ 2
    assert!(Term::equiv(&n_t(), &c()));
}
