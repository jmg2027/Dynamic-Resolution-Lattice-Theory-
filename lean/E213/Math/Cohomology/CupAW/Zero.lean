import E213.Math.Cohomology.CupAW.Core
import E213.Math.Cohomology.Delta.Core

/-!
# Zero lemmas for cupAW and delta

cupAW(0, β) = cupAW(α, 0) = 0
delta(0)    = 0

These are the structural identities needed for the algebraic
lift of Leibniz: when a basis component is "0", the whole
cup/delta product collapses.
-/

namespace E213.Math.Cohomology.CupAW.Zero

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.Core (cupAW)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Hodge.Involution (v0_5)

/-- cupAW with zero left = zero, universally. -/
theorem cupAW_zero_left (n a b : Nat) (β : Cochain n b)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b (Cochain.zero n a) β τ_idx = false := by
  simp only [cupAW, Cochain.zero]
  by_cases hf : subsetIdx n a ((kSubset n (a + b - 1) τ_idx.val).take a) < binom n a
  · by_cases hb : subsetIdx n b ((kSubset n (a + b - 1) τ_idx.val).drop (a - 1)) < binom n b
    · simp [hf, hb]
    · simp [hf, hb]
  · simp [hf]

/-- cupAW with zero right = zero, universally. -/
theorem cupAW_zero_right (n a b : Nat) (α : Cochain n a)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b α (Cochain.zero n b) τ_idx = false := by
  simp only [cupAW, Cochain.zero]
  by_cases hf : subsetIdx n a ((kSubset n (a + b - 1) τ_idx.val).take a) < binom n a
  · by_cases hb : subsetIdx n b ((kSubset n (a + b - 1) τ_idx.val).drop (a - 1)) < binom n b
    · simp [hf, hb]
    · simp [hf, hb]
  · simp [hf]

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
    show tl.foldl _ _ = acc
    by_cases h : subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx hd) < binom n k
    · -- step preserves acc since xor acc false = acc
      have hstep : (xor acc (Cochain.zero n k ⟨_, h⟩)) = acc := by
        show xor acc false = acc
        cases acc <;> rfl
      simp [h, hstep, ih]
    · simp [h, ih]

end E213.Math.Cohomology.CupAW.Zero
