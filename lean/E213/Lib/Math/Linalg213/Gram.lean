import E213.Lib.Math.Linalg213.Vector

/-!
# 213 Linear Algebra — Gram matrix Lens

Given N vectors `v_1, ..., v_N : Vec d`, the Gram matrix
`G : Fin N → Fin N → Nat` is defined by

  G(i, j) = ⟨v_i, v_j⟩ = Σ_{k=0}^{d-1} v_i(k) · v_j(k)

This is the *213-internal* matrix of pairwise inner products.

Key target (chiral compression):
  **rank(G) ≤ d = 5** for any N ≥ 1.
Rank-5 compression means any collection of Gram matrices has
Lens rank ≤ 5 in the linear-combination Lens.

This file establishes the Gram Lens definition + basic identities.
Rank consequences appear when we add the linear-dependence reading
(`Rank.lean`).
-/

namespace E213.Lib.Math.Linalg213.Gram

open E213.Lib.Math.Linalg213.Vector

/-- Inner product (213-native): Σ vᵢ · wᵢ over ℕ, computed via
    `List.range` for `decide`-friendliness. -/
def Vec.inner {n : Nat} (v w : Vec n) : Nat :=
  ((List.range n).map (fun i =>
    if h : i < n then v ⟨i, h⟩ * w ⟨i, h⟩ else 0)).foldl (· + ·) 0

/-- Smoke: ⟨e_0, e_0⟩ = 1 in Vec 5. -/
theorem inner_e0_e0 : Vec.inner e0_5 e0_5 = 1 := by decide

/-- Smoke: ⟨e_0, e_1⟩ = 0 in Vec 5 (orthogonal basis). -/
theorem inner_e0_e1 : Vec.inner e0_5 e1_5 = 0 := by decide

/-- Smoke: ⟨e_0 + e_1, e_0 + e_1⟩ = 2. -/
theorem inner_basis_sum : Vec.inner (Vec.add e0_5 e1_5) (Vec.add e0_5 e1_5) = 2 := by
  decide

/-- Inner product is symmetric. Pointwise: ⟨v, w⟩ = ⟨w, v⟩.
    Decide-checked at Vec 5 for chosen pairs. -/
theorem inner_symm_e0_e1 : Vec.inner e0_5 e1_5 = Vec.inner e1_5 e0_5 := by decide

/-- Gram matrix of a finite collection of N vectors in Vec d. -/
def Gram (N d : Nat) (vs : Fin N → Vec d) : Fin N → Fin N → Nat :=
  fun i j => Vec.inner (vs i) (vs j)

/-- A 2-vector collection in Vec 5: [e_0, e_1].  PURE via if-then-else
    on `i.val` (Fin pattern match would leak propext via exhaustiveness). -/
def vs2 : Fin 2 → Vec 5 := fun i =>
  if i.val = 0 then e0_5 else e1_5

/-- Smoke: Gram of [e_0, e_1] is the 2x2 identity over ℕ. -/
theorem gram_orthonormal_2 :
    Gram 2 5 vs2 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1
    ∧ Gram 2 5 vs2 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0
    ∧ Gram 2 5 vs2 ⟨1, by decide⟩ ⟨0, by decide⟩ = 0
    ∧ Gram 2 5 vs2 ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by decide

/-- ★ Target (not yet proven): for any N and any vector
    collection `vs : Fin N → Vec 5`, the Gram matrix has rank ≤ 5.
    This is the **paper 1 chiral compression theorem** in its
    213-internal form.  Awaits `Rank.lean`. -/
theorem rank_5_compression_target : True := trivial

end E213.Lib.Math.Linalg213.Gram
