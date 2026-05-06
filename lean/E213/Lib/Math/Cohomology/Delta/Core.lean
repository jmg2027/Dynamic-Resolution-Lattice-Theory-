import E213.Lib.Math.Cohomology.SimplexBasis
import E213.Lib.Math.Cohomology.Cochain.Core

import E213.Lib.Physics.Simplex.Counts
/-!
# Cohomology — coboundary δ : Cᵏ → Cᵏ⁺¹

The simplicial coboundary with ℤ/2 coefficients (XOR alternating sum).

For a (k+1)-subset τ of {0..n-1}, the coboundary value δσ(τ) is

    δσ(τ) = XOR_{i=0..k} σ(τ \ {τ[i]})

where τ[i] is the i-th vertex of τ in sorted order, and τ \ {τ[i]}
is the k-subset obtained by removing it.  In ℤ/2 the alternating
sign (-1)^i becomes identity, so the alternating sum collapses to
XOR — which is exactly what makes δ²=0 still hold in mod-2.
-/

namespace E213.Lib.Math.Cohomology.Delta.Core

open E213.Lib.Physics.Simplex.Counts (binom d NS NT)
open E213.Lib.Math.Cohomology.SimplexBasis
open E213.Lib.Math.Cohomology.Cochain.Core

/-- The colex index of a sorted k-subset `s` of {0..n-1}.
    Brute-force linear search through `Fin (binom n k)`.
    Returns `binom n k` (out-of-range) if not found. -/
def subsetIdx (n k : Nat) (s : List Nat) : Nat :=
  ((List.range (binom n k)).find? (fun i => kSubset n k i == s)).getD (binom n k)

/-- Smoke: subsetIdx of [0,1] at n=3 k=2 is 0. -/
theorem subsetIdx_01 : subsetIdx 3 2 [0, 1] = 0 := by decide

/-- Smoke: subsetIdx of [1,2] at n=3 k=2 is 2. -/
theorem subsetIdx_12 : subsetIdx 3 2 [1, 2] = 2 := by decide

/-- Smoke: subsetIdx of [3,4] at n=5 k=2 is 9 (last). -/
theorem subsetIdx_34_d5 : subsetIdx 5 2 [3, 4] = 9 := by decide

/-- δ at a single (k+1)-subset (raw Nat index): XOR over face values. -/
def deltaAt (n k : Nat) (σ : Cochain n k) (τ_idx : Nat) : Bool :=
  let τ := kSubset n (k + 1) τ_idx
  ((List.range (k + 1)).foldl
    (fun acc i =>
      let face_i := τ.eraseIdx i
      let f_idx := subsetIdx n k face_i
      if h : f_idx < binom n k then
        xor acc (σ ⟨f_idx, h⟩)
      else acc)
    false)

/-- Coboundary δ: Cᵏ → Cᵏ⁺¹. -/
def delta {n k : Nat} (σ : Cochain n k) : Cochain n (k + 1) :=
  fun τ_idx => deltaAt n k σ τ_idx.val

/-- Concrete: δ of the indicator on vertex 0 in n=3.  Edges
    incident to 0 are [0,1] and [0,2]; non-incident is [1,2]. -/
def vertex0_n3 : Cochain 3 1 := fun i => i.val = 0

theorem delta_vertex0_n3_01 :
    delta vertex0_n3 ⟨0, by decide⟩ = true := by decide

theorem delta_vertex0_n3_02 :
    delta vertex0_n3 ⟨1, by decide⟩ = true := by decide

theorem delta_vertex0_n3_12 :
    delta vertex0_n3 ⟨2, by decide⟩ = false := by decide

end E213.Lib.Math.Cohomology.Delta.Core
