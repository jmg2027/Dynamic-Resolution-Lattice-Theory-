import E213.Lib.Math.Real213.CutSumTest

/-!
# Real213 — factorial + `cutInvFactorial`

`Nat`-only factorial helpers used for the Taylor series of `cutExp`.

`factorial n = n!` and `cutInvFactorial n = constCut 1 n!` are
fully primitive — no `Nat.factorial`-from-Mathlib (which would
trigger propext via simp paths).

Used by `Real213.CutExpSeries` to weight Taylor terms `x^n / n!`.
-/

namespace E213.Lib.Math.Real213.CutFactorial

open E213.Lib.Math.Real213.CutSumTest (constCut)

/-- 213-native factorial: `factorial 0 = 1`, `factorial (n+1) = (n+1) · factorial n`. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- `factorial 0 = 1` (rfl). -/
theorem factorial_zero : factorial 0 = 1 := rfl

/-- `factorial 1 = 1` (rfl). -/
theorem factorial_one : factorial 1 = 1 := rfl

/-- `factorial 2 = 2`. -/
theorem factorial_two : factorial 2 = 2 := rfl

/-- `factorial (n+1) = (n+1) · factorial n` (rfl). -/
theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := rfl

/-- Factorial is positive for every `n`. -/
theorem factorial_pos : ∀ n, 0 < factorial n
  | 0 => Nat.zero_lt_succ 0
  | n + 1 =>
    let ih : 0 < factorial n := factorial_pos n
    let h1 : 0 < n + 1 := Nat.zero_lt_succ n
    Nat.mul_pos h1 ih

/-- `cutInvFactorial n = 1 / n!` as a constant cut. -/
def cutInvFactorial (n : Nat) : Nat → Nat → Bool := constCut 1 (factorial n)

/-- `cutInvFactorial 0 = constCut 1 1` (rfl). -/
theorem cutInvFactorial_zero : cutInvFactorial 0 = constCut 1 1 := rfl

/-- `cutInvFactorial 1 = constCut 1 1` (factorial 1 = 1, rfl). -/
theorem cutInvFactorial_one : cutInvFactorial 1 = constCut 1 1 := rfl

/-- `cutInvFactorial 2 = constCut 1 2`. -/
theorem cutInvFactorial_two : cutInvFactorial 2 = constCut 1 2 := rfl

end E213.Lib.Math.Real213.CutFactorial
