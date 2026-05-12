import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Math.Cohomology.SimplexBasis
import E213.Lib.Physics.Simplex.Counts
/-!
# Zero lemmas for cupAW and delta

cupAW(0, β) = cupAW(α, 0) = 0
delta(0)    = 0

These are the structural identities needed for the algebraic
lift of Leibniz: when a basis component is "0", the whole
cup/delta product collapses.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Zero

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta deltaAt subsetIdx)
open E213.Lib.Math.Cohomology.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)

/-- cupAW with zero left = zero, universally. -/
theorem cupAW_zero_left (n a b : Nat) (β : Cochain n b)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b (Cochain.zero n a) β τ_idx = false := by
  unfold cupAW Cochain.zero
  match (inferInstance : Decidable
      (subsetIdx n a ((kSubset n (a + b - 1) τ_idx.val).take a) < binom n a)) with
  | .isTrue hf =>
    rw [dif_pos hf]
    match (inferInstance : Decidable
        (subsetIdx n b ((kSubset n (a + b - 1) τ_idx.val).drop (a - 1)) < binom n b)) with
    | .isTrue hb => rw [dif_pos hb]; rfl
    | .isFalse hb => rw [dif_neg hb]
  | .isFalse hf => rw [dif_neg hf]

/-- cupAW with zero right = zero, universally. -/
theorem cupAW_zero_right (n a b : Nat) (α : Cochain n a)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b α (Cochain.zero n b) τ_idx = false := by
  unfold cupAW Cochain.zero
  match (inferInstance : Decidable
      (subsetIdx n a ((kSubset n (a + b - 1) τ_idx.val).take a) < binom n a)) with
  | .isTrue hf =>
    rw [dif_pos hf]
    match (inferInstance : Decidable
        (subsetIdx n b ((kSubset n (a + b - 1) τ_idx.val).drop (a - 1)) < binom n b)) with
    | .isTrue hb =>
      rw [dif_pos hb]
      exact Bool.and_false _
    | .isFalse hb => rw [dif_neg hb]
  | .isFalse hf => rw [dif_neg hf]

/-- delta of zero = zero, universally. -/
theorem delta_zero (n k : Nat)
    (τ_idx : Fin (binom n (k + 1))) :
    delta (Cochain.zero n k) τ_idx = false := by
  show deltaAt n k (Cochain.zero n k) τ_idx.val = false
  unfold deltaAt
  -- Cochain.zero gives σ ⟨..⟩ = false; xor acc false = acc.  Foldl
  -- of a function that always returns acc on false starting acc =
  -- false stays false.
  suffices h : ∀ (xs : List Nat) (acc : Bool),
      xs.foldl (fun acc i =>
        let face_i := (kSubset n (k+1) τ_idx.val).eraseIdx i
        let f_idx := subsetIdx n k face_i
        if h : f_idx < binom n k then
          xor acc (Cochain.zero n k ⟨f_idx, h⟩)
        else acc) acc = acc by
    exact h (List.range (k+1)) false
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons hd tl ih =>
    intro acc
    show tl.foldl _
      (if h : subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx hd) < binom n k
       then xor acc ((Cochain.zero n k) ⟨_, h⟩) else acc) = acc
    match (inferInstance : Decidable
        (subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx hd) < binom n k)) with
    | .isTrue h =>
      rw [dif_pos h]
      have hstep : xor acc ((Cochain.zero n k) ⟨_, h⟩) = acc := by
        show xor acc false = acc
        cases acc <;> rfl
      rw [hstep]
      exact ih acc
    | .isFalse h =>
      rw [dif_neg h]
      exact ih acc

end E213.Lib.Math.Cohomology.CupAW.Zero
