import E213.Kernel.Tactic.Nat213
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest

/-!
# Research.Real213ConstCutScale: const cut scaling theorem

constCut a b = constCut (a*c) (b*c) for c ≥ 1.

Equivalent rationals (1/2 = 2/4 = 3/6 = ...) yield same cut function.
-/

namespace E213.Math.Real213.ConstCutScale

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSumTest (constCut)

/-- **constCut scaling pointwise**: ∀ m k, constCut a b m k = constCut (a*c) (b*c) m k.
    ∅-axiom: pointwise variant (no funext).  Decides on the underlying
    Nat inequality `a*k ≤ b*m` via `Nat.le_or_lt` (avoids by_cases). -/
theorem constCut_scale_at (a b c : Nat) (hc : c ≥ 1) (m k : Nat) :
    constCut a b m k = constCut (a*c) (b*c) m k := by
  show decide (a*k ≤ b*m) = decide ((a*c)*k ≤ (b*c)*m)
  -- Bridge: (a*c)*k = c*(a*k), (b*c)*m = c*(b*m).
  have e1 : (a*c)*k = c*(a*k) := by
    rw [Nat.mul_comm a c, E213.Tactic.Nat213.mul_assoc]
  have e2 : (b*c)*m = c*(b*m) := by
    rw [Nat.mul_comm b c, E213.Tactic.Nat213.mul_assoc]
  rcases Nat.lt_or_ge (b*m) (a*k) with hlt | hge
  · -- a*k > b*m: both decide give false.
    have hnot : ¬ (a*k ≤ b*m) := Nat.not_le_of_lt hlt
    have hnot' : ¬ ((a*c)*k ≤ (b*c)*m) := by
      intro habs
      apply hnot
      rw [e1, e2] at habs
      exact Nat.le_of_mul_le_mul_left habs hc
    rw [decide_eq_false hnot, decide_eq_false hnot']
  · -- a*k ≤ b*m: both decide give true.
    have h' : (a*c)*k ≤ (b*c)*m := by
      rw [e1, e2]
      exact Nat.mul_le_mul_left c hge
    rw [decide_eq_true hge, decide_eq_true h']

/-- **constCut scaling**: constCut a b = constCut (a*c) (b*c) for c ≥ 1.
    Function-equality form (uses `funext` — DIRTY).  Prefer the
    pointwise `constCut_scale_at` for ∅-axiom downstream. -/
theorem constCut_scale (a b c : Nat) (hc : c ≥ 1) :
    constCut a b = constCut (a*c) (b*c) :=
  funext fun m => funext fun k => constCut_scale_at a b c hc m k

/-- 1/2 = 2/4. -/
example : constCut 1 2 = constCut 2 4 := constCut_scale 1 2 2 (by decide)

/-- 1/2 = 3/6. -/
example : constCut 1 2 = constCut 3 6 := constCut_scale 1 2 3 (by decide)

/-- 2/3 = 4/6. -/
example : constCut 2 3 = constCut 4 6 := constCut_scale 2 3 2 (by decide)

/-- constCut 1 1 = constCut a a (= "1") for a ≥ 1. -/
theorem constCut_one_one_eq (a : Nat) (ha : a ≥ 1) :
    constCut 1 1 = constCut a a := by
  have h := constCut_scale 1 1 a ha
  rw [Nat.one_mul] at h
  exact h

/-- constCut 0 1 = constCut 0 b (= "0") for b ≥ 1. -/
theorem constCut_zero_eq (b : Nat) (hb : b ≥ 1) :
    constCut 0 1 = constCut 0 b := by
  have h := constCut_scale 0 1 b hb
  rw [Nat.zero_mul, Nat.one_mul] at h
  exact h

end E213.Math.Real213.ConstCutScale
