/-!
# Reverse Mathematics 213 — Phase GA: omniscience principles

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`), Phase GA.

The residue's decision carrier is `Nat → Bool` (a test / predicate / `Object1` row).  An
**omniscience principle** is a claim to *decide* something infinitary about such a stream —
the "freeze a transition into a verdict" move the residue refuses
(`theory/essays/foundations/the_one_diagonal.md`).  213 does not prove these; it states them
as `Prop`s and calibrates everything against them.  This file fixes the base of the ledger:
the principles `LPO / WLPO / MP / LLPO` and the ∅-axiom implications between them (the
constructive deductions that hold with *no* omniscience — the residue's free interior).

Pure-Lean note: `Bool.noConfusion` / `absurd`, never `Nat.succ_ne_zero` (the latter pulls
`propext` in this Mathlib-free kernel).

Next (Phase GB): `InfChildExists` (`Lib/Math/Combinatorics/KonigConditional.lean`) as an
LLPO-instance — the König/compactness calibration tightened.
-/

namespace E213.Lib.Math.Logic

/-- **LPO** (Limited Principle of Omniscience): every decision stream either fires
    somewhere or is everywhere false.  The strongest of the base principles. -/
def LPO : Prop := ∀ f : Nat → Bool, (∃ n, f n = true) ∨ (∀ n, f n = false)

/-- **WLPO** (Weak LPO): "everywhere false" is decidable (as a `∨ ¬`). -/
def WLPO : Prop := ∀ f : Nat → Bool, (∀ n, f n = false) ∨ ¬ (∀ n, f n = false)

/-- **MP** (Markov's Principle): not-everywhere-false yields an explicit witness. -/
def MP : Prop := ∀ f : Nat → Bool, ¬ (∀ n, f n = false) → ∃ n, f n = true

/-- **LLPO** (Lesser LPO): for an at-most-one-true stream, the (possible) true index is
    even or odd.  Strictly weaker than LPO; the rung the König child-disjunction sits at. -/
def LLPO : Prop := ∀ f : Nat → Bool,
  (∀ m n, f m = true → f n = true → m = n) →
  (∀ k, f (2 * k) = false) ∨ (∀ k, f (2 * k + 1) = false)

/-- ★ **LPO ⟹ WLPO**, ∅-axiom.  A fire-witness refutes "everywhere false". -/
theorem lpo_imp_wlpo (h : LPO) : WLPO :=
  fun f => (h f).elim
    (fun he => Or.inr (fun hall =>
      he.elim (fun n hn => Bool.noConfusion (hn.symm.trans (hall n)))))
    (fun hall => Or.inl hall)

/-- ★ **LPO ⟹ MP**, ∅-axiom.  The "everywhere false" alternative is absurd under the
    hypothesis, so LPO's witness alternative must hold. -/
theorem lpo_imp_mp (h : LPO) : MP :=
  fun f hnot => (h f).elim (fun he => he) (fun hall => absurd hall hnot)

end E213.Lib.Math.Logic
