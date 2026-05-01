import E213.Math.Cohomology.Delta.Core

/-!
# Cohomology — Hodge ⋆ at cochain level (Phase CB, file 1)

The Hodge star ⋆: Cᵏ(Δⁿ⁻¹) → Cⁿ⁻ᵏ(Δⁿ⁻¹) maps each cochain on
k-subsets to its set-theoretic-complement cochain on (n−k)-subsets.

In ℤ/2 (Bool/XOR) coefficients, the usual sign factor (−1)^(k(n−k))
collapses to identity, so ⋆ is simply

    (⋆σ)(T) = σ(complement T)

at every (n−k)-subset T.  Combined with `subsetIdx` (Phase CA), this
gives a concrete decidable Lean definition.

`SimplexCounts.hodge_*` already proved Hodge dim duality
`binom n k = binom n (n−k)`; this file lifts that to the cochain
*action* level.
-/

namespace E213.Math.Cohomology.Hodge.Star

open E213.Physics.Simplex.Counts (binom d NS NT)

/-- Set-theoretic complement of a sorted subset within {0..n-1}.
    Returns the sorted list of vertices NOT in `s`. -/
def listComplement (n : Nat) (s : List Nat) : List Nat :=
  (List.range n).filter (fun v => !s.contains v)

/-- Smoke: complement of [0,1] in {0,1,2} is [2]. -/
theorem listComp_01_in_3 : listComplement 3 [0, 1] = [2] := by decide

/-- Smoke: complement of [3,4] in {0..4} is [0,1,2]. -/
theorem listComp_34_in_5 : listComplement 5 [3, 4] = [0, 1, 2] := by decide

/-- Smoke: complement of [] in {0..4} is everything. -/
theorem listComp_empty_in_5 :
    listComplement 5 [] = [0, 1, 2, 3, 4] := by decide

/-- The colex index of the complement of the i-th k-subset of
    {0..n-1}, viewed as an (n-k)-subset.  Returns `binom n (n-k)`
    (out-of-range) if the lookup fails. -/
def complementIdx (n k i : Nat) : Nat :=
  subsetIdx n (n - k) (listComplement n (kSubset n k i))

/-- Smoke: complement of 0-th 1-subset [0] in n=3 is [1,2], colex
    index 2 in the 2-subsets of {0,1,2}. -/
theorem complementIdx_01 : complementIdx 3 1 0 = 2 := by decide

/-- Smoke: complement of last 2-subset [3,4] in n=5 is [0,1,2],
    which is the 0-th 3-subset of {0..4}. -/
theorem complementIdx_last_2_5 : complementIdx 5 2 9 = 0 := by decide

/-- Hodge ⋆ on cochains: (⋆σ)(T) = σ(complement T).
    Type: Cᵏ → Cᵐ where m is explicit (to avoid Nat-subtraction
    elaboration ambiguity at use sites).  Caller must supply
    `m = n - k` (typically as a literal). -/
def hodgeStar (n k m : Nat) (σ : Cochain n k) : Cochain n m :=
  fun j =>
    let c_idx := complementIdx n m j.val
    if h : c_idx < binom n k then
      σ ⟨c_idx, h⟩
    else
      false

/-- Smoke: ⋆ of vertex0_n3 at complement edge [1,2] (idx 2) = true. -/
theorem hodge_vertex0_n3_at_12 :
    hodgeStar 3 1 2 vertex0_n3 ⟨2, by decide⟩ = true := by decide

/-- Smoke: ⋆ of vertex0_n3 at complement edge [0,1] (idx 0) = false. -/
theorem hodge_vertex0_n3_at_01 :
    hodgeStar 3 1 2 vertex0_n3 ⟨0, by decide⟩ = false := by decide

end E213.Math.Cohomology.Hodge.Star
