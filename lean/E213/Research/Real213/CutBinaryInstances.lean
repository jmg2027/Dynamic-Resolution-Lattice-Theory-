import E213.Research.Real213.CutBinary
import E213.Research.Real213.CutSumTest

/-!
# Research.Real213CutBinaryInstances: cutSum / cutMul as generic instances

Demonstrates 213-style generic kernel: specific operations as
parameterizations of `cutBinary`.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **cutSum via generic**: m1+m2 = 2m predicate, k1=k2=2k. -/
def cutSumViaBinary (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  cutBinary (fun m1 m2 => decide (m1 + m2 = 2*m)) (2*k) (2*k) (2*m) (2*m) cx cy

/-- **cutMul via generic**: m1*m2 ≤ m*k predicate, k1=k2=k. -/
def cutMulViaBinary (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  let b := (m+1) * (k+1)
  cutBinary (fun m1 m2 => decide (m1 * m2 ≤ m * k)) k k b b cx cy

/-- 1 + 1 = 2 ≤ 2/1, via generic. -/
example : cutSumViaBinary (constCut 1 1) (constCut 1 1) 2 1 = true := by decide

/-- 1 + 1 = 2, NOT ≤ 1/1. -/
example : cutSumViaBinary (constCut 1 1) (constCut 1 1) 1 1 = false := by decide

/-- (1/2) + (1/3) = 5/6 ≤ 1/1. -/
example : cutSumViaBinary (constCut 1 2) (constCut 1 3) 1 1 = true := by decide

/-- 1 * 1 = 1 ≤ 1/1, via generic. -/
example : cutMulViaBinary (constCut 1 1) (constCut 1 1) 1 1 = true := by decide

/-- (1/2)*(1/2) = 1/4 ≤ 1/4, via generic. -/
example : cutMulViaBinary (constCut 1 2) (constCut 1 2) 1 4 = true := by decide

end E213.Research.Real213.CutSum
