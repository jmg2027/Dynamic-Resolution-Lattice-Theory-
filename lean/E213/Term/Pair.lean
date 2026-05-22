import E213.Term.Term

/-!
# Term.Pair — pairwise distinguishability primitive

Per `seed/AXIOM/02_axiom.md` §2.2 clause 2: "pairing of two
somethings is yet another something".  This file represents the
binary distinguishability check `G(i, j)` via a Lens identity:

  G(i,j) = 0  if i ≡ j  (diagonal, self-identity)
  G(i,j) = 1  if i ≢ j  (off-diagonal, distinguishable)

Uses only `Bool.cond` → 0 axiom maintained.
-/

namespace E213.Term.Term

/-- Lens distinguishability primitive: G_ij ∈ {0, 1}. -/
protected def pair (a b : Term) : Term :=
  cond (Term.equiv a b) zero (succ zero)

/-- Off-diagonal count: G value of a pair of two distinct Terms. -/
protected def offDiag (a b : Term) : Term := Term.pair a b

end E213.Term.Term

namespace E213.Term.Pair

open Term

/-- Pair with itself = 0 (diagonal). -/
theorem pair_self_nS : Term.equiv (Term.pair Term.nS Term.nS) zero = true := rfl
theorem pair_self_d  : Term.equiv (Term.pair Term.d  Term.d ) zero = true := rfl

/-- Pair of distinct entities = 1 (off-diagonal). -/
theorem pair_nS_nT : Term.equiv (Term.pair Term.nS Term.nT) (succ zero) = true := rfl
theorem pair_nS_d  : Term.equiv (Term.pair Term.nS Term.d ) (succ zero) = true := rfl
theorem pair_nT_d  : Term.equiv (Term.pair Term.nT Term.d ) (succ zero) = true := rfl

/-- Symmetry: G(i,j) = G(j,i). -/
theorem pair_symm_nS_nT :
    Term.equiv (Term.pair Term.nS Term.nT) (Term.pair Term.nT Term.nS) = true := rfl

/-- Sum of self-pairs = 0 (diagonal trace). -/
theorem diag_trace_zero :
    Term.equiv (add (Term.pair Term.nS Term.nS) (add (Term.pair Term.nT Term.nT) (Term.pair Term.d Term.d))) zero = true := rfl

/-- Number of off-diagonal pairs of d×d entities = d²-d = 20.
    Here via direct arithmetic: 5·5 - 5 = 20. -/
theorem off_count_d :
    Term.eval (mul Term.d (succ (succ (succ (succ zero))))) = 20 := rfl

/-- Number of pairs in (n_S, n_T) bipartite K_{3,2} = 6. -/
theorem K32_pairs : Term.eval (mul Term.nS Term.nT) = 6 := rfl

end E213.Term.Pair

#print axioms E213.Term.Pair.pair_self_nS
#print axioms E213.Term.Pair.pair_self_d
#print axioms E213.Term.Pair.pair_nS_nT
#print axioms E213.Term.Pair.pair_nS_d
#print axioms E213.Term.Pair.pair_nT_d
#print axioms E213.Term.Pair.pair_symm_nS_nT
#print axioms E213.Term.Pair.diag_trace_zero
#print axioms E213.Term.Pair.off_count_d
#print axioms E213.Term.Pair.K32_pairs
