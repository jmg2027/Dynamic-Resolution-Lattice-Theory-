//! Integration tests — paper 1 chiral compression mirror.
//!
//! Maps to `Math/Cohomology/TopologyCompare.lean`, `Paper1Chiral.lean`,
//! `Linalg213/Capstone.lean`.

use drlt_theory::{check_not_eq, Raw};
use drlt_lens::{
    b1_bipartite, binom, chiral_dim, lens_st_count, paper1_capstone_check,
    chiral_k32::{NS, NT, D},
};

fn slash(x: Raw, y: Raw) -> Raw {
    let w = check_not_eq(&x, &y).expect("x ≠ y");
    Raw::slash(x, y, w)
}

#[test] fn atomic_constants() {
    assert_eq!(NS, 3); assert_eq!(NT, 2); assert_eq!(D, 5);
    assert_eq!(NS + NT, D);
}

// ── b1_bipartite Lean lemma mirrors ───────────────────────────────

/// Lean: `K32_c1_b1 : b1_bipartite 3 2 1 = 2`.
#[test] fn k32_c1_b1() { assert_eq!(b1_bipartite(3, 2, 1), 2); }
/// Lean: `K32_c2_b1 : b1_bipartite 3 2 2 = 8`.
#[test] fn k32_c2_b1() { assert_eq!(b1_bipartite(3, 2, 2), 8); }
/// Lean: `K32_c3_b1 : b1_bipartite 3 2 3 = 14`.
#[test] fn k32_c3_b1() { assert_eq!(b1_bipartite(3, 2, 3), 14); }
/// Lean: `K41_c2_b1 : b1_bipartite 4 1 2 = 4`.
#[test] fn k41_c2_b1() { assert_eq!(b1_bipartite(4, 1, 2), 4); }
/// Lean: `K23_c2_b1 : b1_bipartite 2 3 2 = 8`.
#[test] fn k23_c2_b1() { assert_eq!(b1_bipartite(2, 3, 2), 8); }

// ── chiralDim Lean lemma mirrors ──────────────────────────────────

/// Lean: `Paper1Chiral.level0 : chiralDim 0 0 = 1`.
#[test] fn level0() { assert_eq!(chiral_dim(0, 0), 1); }

/// Lean: `level1_chiral_decomp : (1,0)=3 ∧ (0,1)=2 ∧ sum=5`.
#[test] fn level1_chiral_decomp() {
    assert_eq!(chiral_dim(1, 0), 3);
    assert_eq!(chiral_dim(0, 1), 2);
    assert_eq!(chiral_dim(1, 0) + chiral_dim(0, 1), 5);
}

/// Lean: `level2 : (2,0)=3 ∧ (1,1)=6 ∧ (0,2)=1 ∧ sum=10`.
#[test] fn level2_chiral_decomp() {
    assert_eq!(chiral_dim(2, 0), 3);
    assert_eq!(chiral_dim(1, 1), 6);
    assert_eq!(chiral_dim(0, 2), 1);
    assert_eq!(chiral_dim(2, 0) + chiral_dim(1, 1) + chiral_dim(0, 2), 10);
}

#[test] fn binom_basics() {
    assert_eq!(binom(0, 0), 1); assert_eq!(binom(5, 0), 1);
    assert_eq!(binom(5, 5), 1); assert_eq!(binom(5, 6), 0);
    assert_eq!(binom(3, 1), 3); assert_eq!(binom(3, 2), 3);
}

// ── lens_st_count smoke + axiom ───────────────────────────────────

#[test] fn st_count_a()        { assert_eq!(lens_st_count().view(&Raw::a()), (1, 0)); }
#[test] fn st_count_b()        { assert_eq!(lens_st_count().view(&Raw::b()), (0, 1)); }
#[test] fn st_count_slash_ab() {
    assert_eq!(lens_st_count().view(&slash(Raw::a(), Raw::b())), (1, 1));
}
#[test] fn st_count_directionless() {
    let l = lens_st_count();
    assert_eq!(l.view(&slash(Raw::a(), Raw::b())),
               l.view(&slash(Raw::b(), Raw::a())));
}

/// Mirror of `paper1_chiral_compression` numeric conjuncts (i,iii,v,vi).
#[test] fn paper1_capstone_holds() { assert!(paper1_capstone_check()); }
