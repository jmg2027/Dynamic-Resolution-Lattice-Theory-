import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Core.CutPoset
import E213.Meta.Tactic.NatHelper

/-!
# Probability — `ProbabilityCut` (atomic mass)

A *probability cut* is an atomic rational mass `num / den` with
`0 < den` and `num ≤ den`.  It embeds in `FluxCut` as the pure-forward
leg `constCut num den` with zero backward leg.

213-native probability: no Ω, no σ-algebra, no Choice.  The mass is a
`(Nat, Nat)` pair; structure constraints encode "non-negative" and
"bounded by 1".  All facts here are atomic / `rfl`-level — no funext,
no Quot.sound.
-/

namespace E213.Lib.Math.Probability.Foundation.Cut

open E213.Lib.Math.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)

/-- Atomic probability mass: rational `num / den` with `0 < den` and
    `num ≤ den` (mass in [0, 1]). -/
structure ProbabilityCut where
  num : Nat
  den : Nat
  den_pos : 0 < den
  mass_le : num ≤ den

namespace ProbabilityCut

/-- Embed a probability cut as a `FluxCut`: forward = `num/den`,
    backward = `0/1`. -/
def toFlux (p : ProbabilityCut) : FluxCut :=
  FluxCut.ofCut (constCut p.num p.den)

/-- Unit mass `1/1` — total certainty. -/
def unit : ProbabilityCut where
  num := 1
  den := 1
  den_pos := Nat.zero_lt_succ 0
  mass_le := Nat.le_refl 1

/-- Zero mass `0/1` — empty event. -/
def zero : ProbabilityCut where
  num := 0
  den := 1
  den_pos := Nat.zero_lt_succ 0
  mass_le := Nat.zero_le 1

/-- Complementary mass: `a/b ↦ (b − a)/b`. -/
def complement (p : ProbabilityCut) : ProbabilityCut where
  num := p.den - p.num
  den := p.den
  den_pos := p.den_pos
  mass_le := Nat.sub_le p.den p.num

/-- Unit mass forward leg ≡ constant `1/1` (rfl). -/
theorem unit_forward_eq : unit.toFlux.forward = constCut 1 1 := rfl

/-- Zero mass forward leg ≡ constant `0/1` (rfl). -/
theorem zero_forward_eq : zero.toFlux.forward = constCut 0 1 := rfl

/-- Backward leg of any `toFlux` is constant `0/1` (rfl). -/
theorem toFlux_backward (p : ProbabilityCut) :
    p.toFlux.backward = constCut 0 1 := rfl

/-- Complement of unit has forward leg `cutEq` to zero's forward leg. -/
theorem complement_unit_forward :
    cutEq (complement unit).toFlux.forward zero.toFlux.forward :=
  fun _ _ => rfl

/-- Complement of zero has forward leg `cutEq` to unit's forward leg. -/
theorem complement_zero_forward :
    cutEq (complement zero).toFlux.forward unit.toFlux.forward :=
  fun _ _ => rfl

/-- Complement is `num`-involutive: `den − (den − num) = num`. -/
theorem complement_num_involutive (p : ProbabilityCut) :
    (complement (complement p)).num = p.num :=
  E213.Tactic.NatHelper.sub_sub_self p.mass_le

end ProbabilityCut

end E213.Lib.Math.Probability.Foundation.Cut
