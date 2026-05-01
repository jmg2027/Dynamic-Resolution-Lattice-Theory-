import E213.Math.Real213.CutPow
import E213.Math.Real213.CutSeries

/-!
# Research.Real213CutExp: exp series at cut level

exp(x) = Σ_{i=0}^∞ x^i / i!

## Definitions

factorial : Nat → Nat.
expSeries x i := x^i / i! cut.
expCutPartial x n := partialSum expSeries x at n.

## Significance

Partial sum approximation of e^x at cut level.  Convergence proof is a
separate arc.
-/

namespace E213.Math.Real213.CutExp

open E213.Firmware E213.Hypervisor

/-- Factorial. -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

/-- exp series term: x^i / i! cut. -/
def expSeriesTerm (x : Nat → Nat → Bool) (i : Nat) : Nat → Nat → Bool :=
  cutScale 1 (factorial i) (cutPow x i)

/-- Partial sum of exp series at degree n. -/
def expCutPartial (x : Nat → Nat → Bool) (n : Nat) : Nat → Nat → Bool :=
  partialSum (expSeriesTerm x) n

/-- expCutPartial 0 = 0 (empty sum). -/
example (x) : expCutPartial x 0 = constCut 0 1 := rfl

end E213.Math.Real213.CutExp
