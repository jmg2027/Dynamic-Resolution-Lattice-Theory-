import E213.Lib.Math.Cohomology.Universal.Prop41
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Universal δ²=0 Prop-lift at (4, 2) — Δ³ edge cochain

Cochain 4 2 = Fin 6 → Bool, 2⁶ = 64 functions.  Pattern via
6 Bool values.  δ² goes 2 → 3 → 4, codomain Fin (binom 4 4)
= Fin 1.  64 × 1 = 64 evals.
-/

namespace E213.Lib.Math.Cohomology.Universal.Prop42

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

/-- Cochain 4 2 parametrized by 6 Bool values.  PURE via if-then-else
    on `i.val` (Fin pattern match would leak propext/Quot.sound). -/
def pattern (b0 b1 b2 b3 b4 b5 : Bool) : Cochain 4 2 := fun i =>
  if i.val = 0 then b0
  else if i.val = 1 then b1
  else if i.val = 2 then b2
  else if i.val = 3 then b3
  else if i.val = 4 then b4
  else b5

/-- Pointwise pattern equality.  ∅-axiom via `cases_lt_six + subst`. -/
theorem pattern_eq_at (σ : Cochain 4 2) (k : Fin (binom 4 2)) :
    σ k = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                  (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                  (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern _ _ _ _ _ _ ⟨n, hn⟩
  rcases E213.Tactic.NatHelper.cases_lt_six hn
    with h | h | h | h | h | h <;>
    subst h <;> rfl

/-- δ²=0 on every (4, 2) pattern: 64 patterns × 1 index. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ i : Fin (binom 4 4),
      delta (delta (pattern b0 b1 b2 b3 b4 b5)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 4 2, δ²σ = 0.  ∅-axiom — chains
    `pattern_eq_at` through `delta_pointwise_eq` twice (no funext). -/
theorem dsq_zero_prop_4_2 (σ : Cochain 4 2)
    (i : Fin (binom 4 4)) : delta (delta σ) i = false :=
  let p := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                   (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                   (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
  let h_pw : ∀ k, σ k = p k := pattern_eq_at σ
  let h_delta_pw : ∀ k, delta σ k = delta p k :=
    fun k => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              σ p h_pw k
  let h_dd : delta (delta σ) i = delta (delta p) i :=
    E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
      (delta σ) (delta p) h_delta_pw i
  h_dd.trans (dsq_pattern _ _ _ _ _ _ i)

end E213.Lib.Math.Cohomology.Universal.Prop42
