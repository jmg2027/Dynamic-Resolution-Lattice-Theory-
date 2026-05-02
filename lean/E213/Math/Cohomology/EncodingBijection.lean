import E213.Math.Cohomology.Universal.Prop51
import E213.Math.Cohomology.BettiKernel

/-!
# Encoding bijection at (5, 1) — alternative Prop-lift route

User: hard deferred items 될때까지 고고.  Encoding bijection
gives an alternative Prop-lift route via `cochainAt` from
`BettiKernel`:

  σ : Cochain 5 1 ↔ encode σ : Fin 32

For each σ, define encode σ as the bit-pattern of σ values.
Then σ pointwise equals cochainAt 5 1 (encode σ).

This connects pattern-based Prop-lift (E213.Math.Cohomology.Universal.Prop51) to
the enumeration-based Bool-level (Universal).
-/

namespace E213.Math.Cohomology.EncodingBijection

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Universal.Prop51 (pattern)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.BettiKernel (cochainAt)

/-- Bool-to-Nat helper. -/
def boolToNat (b : Bool) : Nat := if b then 1 else 0

/-- Encoding: 5 Bool values to Fin 32. -/
def encode_5_1 (σ : Cochain 5 1) : Nat :=
  boolToNat (σ ⟨0, by decide⟩) +
  2 * boolToNat (σ ⟨1, by decide⟩) +
  4 * boolToNat (σ ⟨2, by decide⟩) +
  8 * boolToNat (σ ⟨3, by decide⟩) +
  16 * boolToNat (σ ⟨4, by decide⟩)

/-- Encoding range: 0 ≤ encode σ < 32 (decide-checked smoke). -/
theorem encode_range_smoke :
    encode_5_1 (fun _ => false) = 0
    ∧ encode_5_1 (fun _ => true) = 31 := by decide

/-- The cochainAt encoding pointwise matches σ — verified via
    pattern enumeration: 32 patterns × 5 indices = 160 evals.

    This is the core encoding bijection lemma at (5, 1). -/
theorem encode_pointwise_pattern :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ j : Fin 5,
      pattern b0 b1 b2 b3 b4 j
        = cochainAt 5 1 (encode_5_1 (pattern b0 b1 b2 b3 b4)) j := by
  decide

/-- ★★★ Encoding bijection lifted to ∀ σ : Cochain 5 1.
    For all σ, σ j = cochainAt 5 1 (encode σ) j pointwise.
    ∅-axiom — chains `pattern_eq_at` (pointwise, no funext) with
    `encode_pointwise_pattern`.  The two `encode_5_1` arguments
    agree by `rfl` since `pattern (σ⟨i,_⟩...) ⟨i,_⟩ = σ⟨i,_⟩`. -/
theorem encode_bijection (σ : Cochain 5 1) (j : Fin 5) :
    σ j = cochainAt 5 1 (encode_5_1 σ) j :=
  let h_pw : σ j = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                           (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                           (σ ⟨4, by decide⟩) j :=
    E213.Math.Cohomology.Universal.Prop51.pattern_eq_at σ j
  h_pw.trans (encode_pointwise_pattern _ _ _ _ _ j)

end E213.Math.Cohomology.EncodingBijection
