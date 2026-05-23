import E213.Lib.Math.Cohomology.Universal.Prop51
import E213.Lib.Math.Cohomology.Universal.Pattern10
import E213.Lib.Math.Cohomology.Delta.Pointwise

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Universal δ²=0 Prop-lift at (5, 2) — Δ⁴ edge cochain case

Cochain 5 2 = Fin (binom 5 2) → Bool = Fin 10 → Bool,
2¹⁰ = 1024 functions.

This is the **Δ⁴ edge cochain** Universal δ²=0 — relevant to
α_em + Yang-Mills mass gap (1-cochain on K_{3,2}^{(2)} edges).

**∅-axiom**: pattern via `Pattern10.pattern10`, `pattern_eq_at`
via `Pattern10.pattern10_eq_at` (COH-1 template), `dsq_zero_prop_5_2`
via `delta_pointwise_eq` chain.
-/

namespace E213.Lib.Math.Cohomology.Universal.Prop52

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.Universal.Pattern10 (pattern10 pattern10_eq_at)

/-- Cochain 5 2 parametrized by 10 Bool values.  Alias for
    `Pattern10.pattern10` (since `Cochain 5 2 = Fin 10 → Bool` defeq). -/
abbrev pattern (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Cochain 5 2 :=
  pattern10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9

/-- Pointwise pattern equality.  PURE corollary of `pattern10_eq_at`. -/
theorem pattern_eq_at (σ : Cochain 5 2) (k : Fin (binom 5 2)) :
    σ k = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
      (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
      (σ ⟨9, by decide⟩) k :=
  pattern10_eq_at σ k

set_option maxHeartbeats 8000000 in
/-- δ²=0 on every pattern: 1024 Bool 10-tuples × 5 indices.
    ∅-axiom (decide on Bool variables; pattern is itself ∅-axiom). -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 4),
        delta (delta (pattern b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 2, δ²σ = 0.  ∅-axiom — chains
    `pattern_eq_at` through `delta_pointwise_eq` twice (no funext). -/
theorem dsq_zero_prop_5_2 (σ : Cochain 5 2)
    (i : Fin (binom 5 4)) : delta (delta σ) i = false :=
  let p := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
                   (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
                   (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
                   (σ ⟨9, by decide⟩)
  let h_pw : ∀ k, σ k = p k := pattern_eq_at σ
  let h_delta_pw : ∀ k, delta σ k = delta p k :=
    fun k => delta_pointwise_eq σ p h_pw k
  let h_dd : delta (delta σ) i = delta (delta p) i :=
    delta_pointwise_eq (delta σ) (delta p) h_delta_pw i
  h_dd.trans (dsq_pattern _ _ _ _ _ _ _ _ _ _ i)

end E213.Lib.Math.Cohomology.Universal.Prop52
