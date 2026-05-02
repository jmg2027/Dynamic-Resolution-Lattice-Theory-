import E213.Math.Cohomology.Universal.Prop52
import E213.Math.Cohomology.BettiKernel

/-!
# Encoding bijection at (5, 2) — Cochain 5 2 ↔ Fin 1024

Same construction as `EncodingBijection.lean` (5, 1), extended
to 10 Bool slots: σ : Cochain 5 2 ≃ encode σ : Nat ∈ [0, 1024).
-/

namespace E213.Math.Cohomology.EncodingBijection52

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Universal.Prop52 (pattern)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.BettiKernel (cochainAt)

/-- Bool-to-Nat helper. -/
def boolToNat (b : Bool) : Nat := if b then 1 else 0

/-- Encoding: 10 Bool values to Nat in [0, 1024). -/
def encode_5_2 (σ : Cochain 5 2) : Nat :=
  boolToNat (σ ⟨0, by decide⟩) +
  2 * boolToNat (σ ⟨1, by decide⟩) +
  4 * boolToNat (σ ⟨2, by decide⟩) +
  8 * boolToNat (σ ⟨3, by decide⟩) +
  16 * boolToNat (σ ⟨4, by decide⟩) +
  32 * boolToNat (σ ⟨5, by decide⟩) +
  64 * boolToNat (σ ⟨6, by decide⟩) +
  128 * boolToNat (σ ⟨7, by decide⟩) +
  256 * boolToNat (σ ⟨8, by decide⟩) +
  512 * boolToNat (σ ⟨9, by decide⟩)

/-- Encoding range smoke. -/
theorem encode_range_smoke :
    encode_5_2 (fun _ => false) = 0
    ∧ encode_5_2 (fun _ => true) = 1023 := by decide

set_option maxHeartbeats 8000000 in
/-- The cochainAt encoding pointwise matches σ — verified via
    pattern enumeration: 1024 patterns × 10 indices = 10240 evals. -/
theorem encode_pointwise_pattern :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ j : Fin 10,
      pattern b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 j
        = cochainAt 5 2
            (encode_5_2 (pattern b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) j := by
  decide

/-- ★★★ Encoding bijection at (5, 2). -/
theorem encode_bijection (σ : Cochain 5 2) (j : Fin 10) :
    σ j = cochainAt 5 2 (encode_5_2 σ) j := by
  rw [E213.Math.Cohomology.Universal.Prop52.pattern_eq σ]
  exact encode_pointwise_pattern _ _ _ _ _ _ _ _ _ _ j

end E213.Math.Cohomology.EncodingBijection52
