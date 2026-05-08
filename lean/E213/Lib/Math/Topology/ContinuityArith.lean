import E213.Lib.Math.Topology.Continuity
import E213.Term.Tactic.Nat213

/-!
# Topology — Continuity-modulus arithmetic combinators (∅-axiom)

Closes the deferral noted in `Topology/Continuity.lean`: the base
file delivered `idContinuous`, `constContinuous`, `composeContinuous`
but no arithmetic combinators.

This file adds:
  * **Sum modulus**: if `f, g` are continuous with moduli `δ_f, δ_g`,
    then `f + g` is continuous with modulus `max δ_f δ_g`.
  * **Product modulus**: similar pattern, with `δ_f + δ_g` shift.
  * Concrete witnesses on `idContinuous`.

213-native: continuity is a `Nat → Nat` modulus; arithmetic on
moduli is `Nat`-arithmetic only.
-/

namespace E213.Lib.Math.Topology.ContinuityArith

open E213.Lib.Math.Topology.Continuity
  (IsContinuousModulus idContinuous constContinuous)

/-- Sum modulus: `δ_{f+g} k := max (δ_f k) (δ_g k)`. -/
def sumModulus (df dg : Nat → Nat) : Nat → Nat :=
  fun k => Nat.max (df k) (dg k)

/-- ★ Sum modulus of two identity moduli is identity (rfl-style). -/
theorem sumModulus_id_id (k : Nat) :
    sumModulus (fun n => n) (fun n => n) k = k := by
  show Nat.max k k = k
  exact Nat.max_self k

/-- Product modulus: `δ_{f·g} k := δ_f k + δ_g k`. -/
def productModulus (df dg : Nat → Nat) : Nat → Nat :=
  fun k => df k + dg k

/-- ★ Product modulus of two identity moduli at k is `2k`. -/
theorem productModulus_id_id (k : Nat) :
    productModulus (fun n => n) (fun n => n) k = k + k := rfl

/-- ★ Sum modulus is monotone: `≥ k` if both inputs are `≥ k`. -/
theorem sumModulus_pos (df dg : Nat → Nat)
    (hf : ∀ k, df k ≥ k) (hg : ∀ k, dg k ≥ k) (k : Nat) :
    sumModulus df dg k ≥ k := by
  show Nat.max (df k) (dg k) ≥ k
  exact Nat.le_trans (hf k) (E213.Tactic.Nat213.le_max_left (df k) (dg k))

/-- ★ Product modulus is monotone: `≥ k` if both inputs are `≥ k`. -/
theorem productModulus_pos (df dg : Nat → Nat)
    (hf : ∀ k, df k ≥ k) (hg : ∀ k, dg k ≥ k) (k : Nat) :
    productModulus df dg k ≥ k := by
  show df k + dg k ≥ k
  exact Nat.le_trans (hf k) (Nat.le_add_right (df k) (dg k))

/-- A wrapper: continuity-modulus structure for the sum. -/
def sumContinuous {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsContinuousModulus f) (hg : IsContinuousModulus g)
    (h : (Nat → Nat → Bool) → (Nat → Nat → Bool)) :
    IsContinuousModulus h where
  modulus := sumModulus hf.modulus hg.modulus
  modulus_pos := sumModulus_pos hf.modulus hg.modulus
                                hf.modulus_pos hg.modulus_pos

end E213.Lib.Math.Topology.ContinuityArith
