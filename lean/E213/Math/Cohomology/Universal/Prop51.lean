import E213.Math.Cohomology.Universal.Prop31
import E213.Math.Cohomology.Delta.Pointwise
import E213.Kernel.Tactic.Nat213

/-!
# Universal δ²=0 Prop-lift at (5, 1) — Δ⁴ vertex cochain case

Cochain 5 1 = Fin 5 → Bool, 2⁵ = 32 functions.  Pattern
parametrization with 5 Bool values gives full enumeration.

This is the **Δ⁴ vertex cochain** Universal δ²=0 — the case
most directly relevant to physics (vertex functions on the
5-vertex atomic substrate).

**∅-axiom**: pattern is defined via `match i.val with` (Nat
match, no `Fin (binom n k)` exhaustivity); the universal lift
chains `pattern_eq_at` through `delta_pointwise_eq` (no funext).
-/

namespace E213.Math.Cohomology.Universal.Prop51

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Tactic.Nat213 (cases_lt_five)

/-- Cochain 5 1 parametrized by 5 Bool values.  Defined via
    `match i.val with` (Nat match) to avoid `Fin (binom 5 1)`
    exhaustivity which leaks `propext` at def-level. -/
def pattern (b0 b1 b2 b3 b4 : Bool) : Cochain 5 1 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | _ => b4

/-- Pointwise pattern equality.  ∅-axiom — uses `cases_lt_five`
    + `subst` instead of `funext`. -/
theorem pattern_eq_at (σ : Cochain 5 1) (k : Fin (binom 5 1)) :
    σ k = pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                  (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                  (σ ⟨4, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern _ _ _ _ _ ⟨n, hn⟩
  rcases cases_lt_five hn with h | h | h | h | h <;> subst h <;> rfl

/-- δ²=0 on every pattern: 32 Bool quintuples × 10 indices.
    ∅-axiom — `decide` ranges over Bool variables; the pattern
    def is itself ∅-axiom. -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i : Fin (binom 5 3),
      delta (delta (pattern b0 b1 b2 b3 b4)) i = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 1, δ²σ = 0.  ∅-axiom — chains
    `pattern_eq_at` (pointwise) through `delta_pointwise_eq` twice
    to lift `dsq_pattern` from Bool patterns to arbitrary σ. -/
theorem dsq_zero_prop_5_1 (σ : Cochain 5 1)
    (i : Fin (binom 5 3)) : delta (delta σ) i = false :=
  let p := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩)
                   (σ ⟨2, by decide⟩) (σ ⟨3, by decide⟩)
                   (σ ⟨4, by decide⟩)
  let h_pw : ∀ k, σ k = p k := pattern_eq_at σ
  let h_delta_pw : ∀ k, delta σ k = delta p k :=
    fun k => delta_pointwise_eq σ p h_pw k
  let h_dd : delta (delta σ) i = delta (delta p) i :=
    delta_pointwise_eq (delta σ) (delta p) h_delta_pw i
  h_dd.trans (dsq_pattern _ _ _ _ _ i)

/-- ★★★ Universal δ²=0 Prop-lift at (5, 1) — Δ⁴ vertex case. -/
theorem prop_lift_5_1_capstone :
    ∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 3),
      delta (delta σ) i = false :=
  dsq_zero_prop_5_1

end E213.Math.Cohomology.Universal.Prop51
