import E213.Lib.Math.Cohomology.Universal.Prop31
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Meta.Tactic.Nat213

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Universal δ²=0 Prop-lift at (4, 1) — Δ³ vertex cochain

Cochain 4 1 = Fin 4 → Bool, 2⁴ = 16 functions.  Pattern parametrize
via 4 Bool values.

This is the Δ³ vertex cochain Universal δ²=0 — bridges the (3, 1)
and (5, 1) cases.
-/

namespace E213.Lib.Math.Cohomology.Universal.Prop41

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

/-- Cochain 4 1 parametrized by 4 Bool values.  PURE via if-then-else
    on `i.val` (Fin pattern match would leak propext/Quot.sound via
    exhaustiveness). -/
def pattern (b0 b1 b2 b3 : Bool) : Cochain 4 1 := fun i =>
  if i.val = 0 then b0
  else if i.val = 1 then b1
  else if i.val = 2 then b2
  else b3

/-- Pointwise pattern equality.  ∅-axiom via `cases_lt_four + subst`. -/
theorem pattern_eq_at (σ : Cochain 4 1) (k : Fin (binom 4 1)) :
    σ k = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                  (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern _ _ _ _ ⟨n, hn⟩
  rcases E213.Tactic.Nat213.cases_lt_four hn with h | h | h | h <;>
    subst h <;> rfl

/-- δ²=0 on every (4, 1) pattern: 16 patterns × 4 indices. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 : Bool, ∀ i : Fin (binom 4 3),
      delta (delta (pattern b0 b1 b2 b3)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 4 1, δ²σ = 0.  ∅-axiom — chains
    `pattern_eq_at` through `delta_pointwise_eq` twice (no funext). -/
theorem dsq_zero_prop_4_1 (σ : Cochain 4 1)
    (i : Fin (binom 4 3)) : delta (delta σ) i = false :=
  let p := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                   (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
  let h_pw : ∀ k, σ k = p k := pattern_eq_at σ
  let h_delta_pw : ∀ k, delta σ k = delta p k :=
    fun k => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              σ p h_pw k
  let h_dd : delta (delta σ) i = delta (delta p) i :=
    E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
      (delta σ) (delta p) h_delta_pw i
  h_dd.trans (dsq_pattern _ _ _ _ i)

end E213.Lib.Math.Cohomology.Universal.Prop41
