import E213.Math.Real213.CutSum

/-!
# Research.Real213CutMul: cut-level multiplication (F2)

F2 from `F0_213_native_arithmetic_synthesis.md`: cut-level multiplication
of two RealCuts.

## Definition

`cutMul cx cy m k` := ∃ m1 ≤ bound, m2 ≤ bound with
  cx(m1, k) ∧ cy(m2, k) ∧ m1*m2 ≤ m*k.

= bounded witness for "L_x * L_y ≤ m/k".

For positive reals, k1 = k2 = k → product (m1*m2) / (k*k) ≤ m/k iff
m1*m2 ≤ m*k.

bound = (m+1)*(k+1) — sufficient search space.
-/

namespace E213.Math.Real213.CutMul

open E213.Firmware E213.Hypervisor
open E213.Research.ArchimedeanCauchy

/-- Inner: iterate m2 from 0 to m2Bound, m1 fixed. -/
def cutMulInner (cx cy : Nat → Nat → Bool) (k m m1 : Nat) : Nat → Bool
  | 0 => cx m1 k && cy 0 k && decide (m1 * 0 ≤ m * k)
  | n+1 => (cx m1 k && cy (n+1) k && decide (m1 * (n+1) ≤ m * k))
            || cutMulInner cx cy k m m1 n

/-- Outer: iterate m1 from 0 to m1Bound. -/
def cutMulOuter (cx cy : Nat → Nat → Bool) (k m m2Bound : Nat) : Nat → Bool
  | 0 => cutMulInner cx cy k m 0 m2Bound
  | n+1 => cutMulInner cx cy k m (n+1) m2Bound
            || cutMulOuter cx cy k m m2Bound n

/-- **cutMul**: product cut of two cuts. -/
def cutMul (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  let bound := (m + 1) * (k + 1)
  cutMulOuter cx cy k m bound bound

end E213.Math.Real213.CutMul
