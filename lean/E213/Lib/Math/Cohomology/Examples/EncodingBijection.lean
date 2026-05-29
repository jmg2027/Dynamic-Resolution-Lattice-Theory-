import E213.Lib.Math.Cohomology.Universal.Prop51
import E213.Lib.Math.Cohomology.Universal.Prop52
import E213.Lib.Math.Cohomology.Examples.BettiKernel

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Encoding bijection at `(5, 1)` and `(5, 2)` — alternative Prop-lift route

For each `σ : Cochain 5 k` (k ∈ {1, 2}), define `encode_5_k σ` as
the bit-pattern of `σ`'s values.  Then `σ j = cochainAt 5 k
(encode_5_k σ) j` pointwise.

This connects pattern-based Prop-lifts
(`Universal.Prop51` / `Universal.Prop52`) to the enumeration-based
Bool-level encoding from `Examples.BettiKernel`.

Two strata in one file, each in its own sub-namespace:
  · `EncodingBijection`   — `(5, 1)` with 5 Bool slots → `Fin 32`
  · `EncodingBijection52` — `(5, 2)` with 10 Bool slots →
                             range `[0, 1024)`
-/

/-! ### §1 — `(5, 1)` encoding bijection -/

namespace E213.Lib.Math.Cohomology.Examples.EncodingBijection

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Universal.Prop51 (pattern)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Examples.BettiKernel (cochainAt)

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

/-- Encoding bijection lifted to ∀ σ : Cochain 5 1.
    For all σ, σ j = cochainAt 5 1 (encode σ) j pointwise.
    ∅-axiom — chains `pattern_eq_at` (pointwise, no funext) with
    `encode_pointwise_pattern`. -/
theorem encode_bijection (σ : Cochain 5 1) (j : Fin 5) :
    σ j = cochainAt 5 1 (encode_5_1 σ) j :=
  let h_pw : σ j = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                           (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                           (σ ⟨4, by decide⟩) j :=
    E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at σ j
  h_pw.trans (encode_pointwise_pattern _ _ _ _ _ j)

end E213.Lib.Math.Cohomology.Examples.EncodingBijection

/-! ### §2 — `(5, 2)` encoding bijection (10 Bool slots → range `[0, 1024)`) -/

namespace E213.Lib.Math.Cohomology.Examples.EncodingBijection52

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Universal.Prop52 (pattern)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Examples.BettiKernel (cochainAt)

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

/-- Encoding bijection at (5, 2).  ∅-axiom — chains
    `pattern_eq_at` (pointwise, no funext) with `encode_pointwise_pattern`. -/
theorem encode_bijection (σ : Cochain 5 2) (j : Fin 10) :
    σ j = cochainAt 5 2 (encode_5_2 σ) j :=
  let h_pw : σ j = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
      (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
      (σ ⟨9, by decide⟩) j :=
    E213.Lib.Math.Cohomology.Universal.Prop52.pattern_eq_at σ j
  h_pw.trans (encode_pointwise_pattern _ _ _ _ _ _ _ _ _ _ j)

end E213.Lib.Math.Cohomology.Examples.EncodingBijection52
