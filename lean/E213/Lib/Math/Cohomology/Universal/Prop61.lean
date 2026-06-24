import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Universal δ²=0 Prop-lift at (6, 1) — Δ⁵ vertex cochain case

Cochain 6 1 = Fin 6 → Bool, 2⁶ = 64 functions.  Pattern
parametrization with 6 Bool values gives full enumeration; δ²
lands in `Cochain 6 3` (`binom 6 3 = 20` indices).

This **widens the verified universal-in-σ band** past the
atomic Δ⁴ (`Prop51`, …, `Prop53` cover `5 k`): the same
pattern + `delta_pointwise_eq` lift now closes the **Δ⁵ vertex
case**, empirical evidence that `δ²=0` holds at *every*
dimension — the gap a fully dimension-free `∀ n k σ` proof
would settle.

**∅-axiom**: `pattern` via `match i.val with` (Nat match, no
`Fin (binom n k)` exhaustivity); the universal lift chains
`pattern_eq_at` through `delta_pointwise_eq` twice (no funext).
-/

namespace E213.Lib.Math.Cohomology.Universal.Prop61

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Tactic.NatHelper (cases_lt_six)

/-- Cochain 6 1 parametrized by 6 Bool values.  Defined via
    `match i.val with` (Nat match) to avoid `Fin (binom 6 1)`
    exhaustivity which leaks `propext` at def-level. -/
def pattern (b0 b1 b2 b3 b4 b5 : Bool) : Cochain 6 1 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | _ => b5

/-- Pointwise pattern equality.  ∅-axiom — uses `cases_lt_six`
    + `subst` instead of `funext`. -/
theorem pattern_eq_at (σ : Cochain 6 1) (k : Fin (binom 6 1)) :
    σ k = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                  (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                  (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern _ _ _ _ _ _ ⟨n, hn⟩
  rcases cases_lt_six hn with h | h | h | h | h | h <;> subst h <;> rfl

/-- δ²=0 on every pattern: 64 Bool sextuples × 20 indices.
    ∅-axiom — `decide` ranges over Bool variables; the pattern
    def is itself ∅-axiom. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ i : Fin (binom 6 3),
      delta (delta (pattern b0 b1 b2 b3 b4 b5)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 6 1, δ²σ = 0.  ∅-axiom — chains
    `pattern_eq_at` (pointwise) through `delta_pointwise_eq` twice
    to lift `dsq_pattern` from Bool patterns to arbitrary σ. -/
theorem dsq_zero_prop_6_1 (σ : Cochain 6 1)
    (i : Fin (binom 6 3)) : delta (delta σ) i = false :=
  let p := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                   (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                   (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
  let h_pw : ∀ k, σ k = p k := pattern_eq_at σ
  let h_delta_pw : ∀ k, delta σ k = delta p k :=
    fun k => delta_pointwise_eq σ p h_pw k
  let h_dd : delta (delta σ) i = delta (delta p) i :=
    delta_pointwise_eq (delta σ) (delta p) h_delta_pw i
  h_dd.trans (dsq_pattern _ _ _ _ _ _ i)

/-- ★★★ Universal δ²=0 Prop-lift at (6, 1) — Δ⁵ vertex case.  The
    verified-band frontier: `δ²=0` for *all* vertex cochains on the
    6-vertex simplex, one dimension past the atomic Δ⁴. -/
theorem prop_lift_6_1_capstone :
    ∀ σ : Cochain 6 1, ∀ i : Fin (binom 6 3),
      delta (delta σ) i = false :=
  dsq_zero_prop_6_1

end E213.Lib.Math.Cohomology.Universal.Prop61
