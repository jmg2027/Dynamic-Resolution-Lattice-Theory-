import E213.Kernel.Term

/-!
# E213.Kernel.Pair — Raw 의 pairwise relation 원시.

CLAUDE.md 공리: "Things exist with pairwise relations.
G_ij = ⟨ψ_i|ψ_j⟩."

Lens identity check 으로 G_ij 표현:
  G(i,j) = 0  if i ≡ j  (대각, self-identity)
  G(i,j) = 1  if i ≢ j  (off-diagonal, distinguishable)

`Bool.cond` 만 사용 → 0 axiom 유지.
-/

namespace E213.Kernel.Term

/-- Lens distinguishability primitive: G_ij ∈ {0, 1}. -/
def pair (a b : Term) : Term :=
  cond (equiv a b) zero (succ zero)

/-- Off-diagonal count: 두 distinct Term 페어의 G 값. -/
def offDiag (a b : Term) : Term := pair a b

end E213.Kernel.Term

namespace E213.Kernel.Pair

open Term

/-- 자기 자신과의 페어 = 0 (대각). -/
theorem pair_self_nS : equiv (pair nS nS) zero = true := rfl
theorem pair_self_d  : equiv (pair d  d ) zero = true := rfl

/-- 서로 다른 entity 페어 = 1 (off-diagonal). -/
theorem pair_nS_nT : equiv (pair nS nT) (succ zero) = true := rfl
theorem pair_nS_d  : equiv (pair nS d ) (succ zero) = true := rfl
theorem pair_nT_d  : equiv (pair nT d ) (succ zero) = true := rfl

/-- 대칭: G(i,j) = G(j,i). -/
theorem pair_symm_nS_nT :
    equiv (pair nS nT) (pair nT nS) = true := rfl

/-- 자기 페어 합 = 0 (대각 trace). -/
theorem diag_trace_zero :
    equiv (add (pair nS nS) (add (pair nT nT) (pair d d))) zero = true := rfl

/-- d×d entity 의 off-diagonal 페어 수 = d²-d = 20.
    여기선 직접 산술로: 5·5 - 5 = 20. -/
theorem off_count_d :
    eval (mul d (succ (succ (succ (succ zero))))) = 20 := rfl

/-- (n_S, n_T) bipartite K_{3,2} 의 페어 수 = 6. -/
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
