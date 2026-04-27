import E213.Kernel.Term

/-!
# E213.Kernel.Pair — pairwise relation primitive of Raw.

CLAUDE.md axiom: "Things exist with pairwise relations.
G_ij = ⟨ψ_i|ψ_j⟩."

Representing G_ij via Lens identity check:
  G(i,j) = 0  if i ≡ j  (diagonal, self-identity)
  G(i,j) = 1  if i ≢ j  (off-diagonal, distinguishable)

Uses only `Bool.cond` → 0 axiom maintained.
-/

namespace E213.Kernel.Term

/-- Lens distinguishability primitive: G_ij ∈ {0, 1}. -/
def pair (a b : Term) : Term :=
  cond (equiv a b) zero (succ zero)

/-- Off-diagonal count: G value of a pair of two distinct Terms. -/
def offDiag (a b : Term) : Term := pair a b

end E213.Kernel.Term

namespace E213.Kernel.Pair

open Term

/-- Pair with itself = 0 (diagonal). -/
theorem pair_self_nS : equiv (pair nS nS) zero = true := rfl
theorem pair_self_d  : equiv (pair d  d ) zero = true := rfl

/-- Pair of distinct entities = 1 (off-diagonal). -/
theorem pair_nS_nT : equiv (pair nS nT) (succ zero) = true := rfl
theorem pair_nS_d  : equiv (pair nS d ) (succ zero) = true := rfl
theorem pair_nT_d  : equiv (pair nT d ) (succ zero) = true := rfl

/-- Symmetry: G(i,j) = G(j,i). -/
theorem pair_symm_nS_nT :
    equiv (pair nS nT) (pair nT nS) = true := rfl

/-- Sum of self-pairs = 0 (diagonal trace). -/
theorem diag_trace_zero :
    equiv (add (pair nS nS) (add (pair nT nT) (pair d d))) zero = true := rfl

/-- Number of off-diagonal pairs of d×d entities = d²-d = 20.
    Here via direct arithmetic: 5·5 - 5 = 20. -/
theorem off_count_d :
    eval (mul d (succ (succ (succ (succ zero))))) = 20 := rfl

/-- Number of pairs in (n_S, n_T) bipartite K_{3,2} = 6. -/
theorem K32_pairs : eval (mul nS nT) = 6 := rfl

end E213.Kernel.Pair

#print axioms E213.Kernel.Pair.pair_self_nS
#print axioms E213.Kernel.Pair.pair_self_d
#print axioms E213.Kernel.Pair.pair_nS_nT
#print axioms E213.Kernel.Pair.pair_nS_d
#print axioms E213.Kernel.Pair.pair_nT_d
#print axioms E213.Kernel.Pair.pair_symm_nS_nT
#print axioms E213.Kernel.Pair.diag_trace_zero
#print axioms E213.Kernel.Pair.off_count_d
#print axioms E213.Kernel.Pair.K32_pairs
