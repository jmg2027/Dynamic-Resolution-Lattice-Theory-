import E213.Math.Cohomology.Hodge.Delta

import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.Delta.Core
import E213.Physics.Simplex.Counts
/-!
# Cohomology — kernel enumeration on cochain spaces (, file 1)

To compute Betti numbers `bₖ = dim H_k = dim ker δ_k − dim im δ_{k−1}`
in ℤ/2 cohomology, we need to enumerate the finite cochain space
Cᵏ = Fin (binom n k) → Bool (size 2^(binom n k)) and count.

For finite-dim vector spaces over ℤ/2, |ker T| = 2^(dim ker T) and
rank-nullity gives dim im = dim source − dim ker.  So computing
`kerSize` at each level suffices.

This file:
  * `bitFn N i j` — j-th bit of i, viewed as Bool function on Fin N
  * `cochainAt n k i` — i-th cochain via bit decomposition
  * `isZeroBool n k σ` — Bool check that σ is the zero cochain
  * `kerSizeDelta n k` — count of σ ∈ Cᵏ with δσ = 0
-/

namespace E213.Math.Cohomology.BettiKernel

open E213.Physics.Simplex.Counts (binom d NS NT)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Core (delta)

/-- j-th bit (Bool) of `i : Nat`. -/
def bitFn (i j : Nat) : Bool := (i / 2^j) % 2 == 1

/-- The i-th cochain in Cᵏ via binary encoding of i. -/
def cochainAt (n k i : Nat) : Cochain n k := fun j => bitFn i j.val

/-- Check σ is the zero cochain (all entries false). -/
def isZeroBool (n k : Nat) (σ : Cochain n k) : Bool :=
  (List.range (binom n k)).all (fun j =>
    if h : j < binom n k then !σ ⟨j, h⟩ else true)

/-- Number of cochains in Cᵏ whose δ is zero (kernel size). -/
def kerSizeDelta (n k : Nat) : Nat :=
  ((List.range (2^(binom n k))).filter
    (fun i => isZeroBool n (k+1) (delta (cochainAt n k i)))).length

/-- ker δ₀ on Δ⁴ (augmented C⁰ has 2 cochains; only σ=0 maps to 0). -/
theorem kerSize_5_0 : kerSizeDelta 5 0 = 1 := by decide

/-- ker δ₁ on Δ⁴: σ ∈ C¹ (32 cochains) — constant cochains have
    all edge differences = 0.  Δ⁴ is the complete graph on 5
    vertices, so constants = {all-zero, all-true} ⇒ |ker δ₁| = 2. -/
theorem kerSize_5_1 : kerSizeDelta 5 1 = 2 := by decide

/-- Reduced ℤ/2 Betti numbers for Δ⁴ (contractible).

    With our augmented convention (binom 5 0 = 1 → C⁰ has dim 1
    representing the empty face / augmentation), the cohomology is
    *reduced*:
      |ker δ_0| = 1 ⇒ dim ker δ_0 = 0
      |ker δ_1| = 2 ⇒ dim ker δ_1 = 1
      dim im δ_0 = dim C⁰ − dim ker δ_0 = 1 − 0 = 1
    So b̃_0 = 0 (= dim ker δ_0) and b̃_1 = 1 − 1 = 0. ✓ -/
theorem reduced_betti_d4_contractible :
    kerSizeDelta 5 0 = 1 ∧ kerSizeDelta 5 1 = 2 := by decide

/-- Smoke: |Cᵏ| = 2^(binom n k) for n=5, k=0..2. -/
theorem cochain_count_d5 :
    2^(binom 5 0) = 2 ∧ 2^(binom 5 1) = 32 ∧ 2^(binom 5 2) = 1024 := by
  decide

/-- Smoke: cochainAt 5 1 0 is the zero cochain. -/
theorem cochainAt_zero_5_1 :
    isZeroBool 5 1 (cochainAt 5 1 0) = true := by decide

/-- Smoke: cochainAt 5 1 31 is the all-true cochain (5 bits set). -/
theorem cochainAt_31_5_1_v0 :
    cochainAt 5 1 31 ⟨0, by decide⟩ = true := by decide

theorem cochainAt_31_5_1_v4 :
    cochainAt 5 1 31 ⟨4, by decide⟩ = true := by decide

end E213.Math.Cohomology.BettiKernel
