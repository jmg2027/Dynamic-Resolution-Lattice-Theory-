import E213.Research.Real213CutMaxMin

/-!
# Research.Real213CutAlgebraic: algebraic properties of cut operations

cutMax, cutMin 의 lattice properties + cut zero/one properties.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- constCut 0 1 always true ("0 ≤ everything"). -/
theorem constCut_zero_always (m k : Nat) : constCut 0 1 m k = true := by
  show decide (0 * k ≤ 1 * m) = true
  rw [Nat.zero_mul]
  exact decide_eq_true (Nat.zero_le _)

/-- cutMax idempotent: max(c, c) = c. -/
theorem cutMax_idempotent (c : Nat → Nat → Bool) : cutMax c c = c := by
  funext m k
  show (c m k && c m k) = c m k
  cases c m k <;> rfl

/-- cutMin idempotent. -/
theorem cutMin_idempotent (c : Nat → Nat → Bool) : cutMin c c = c := by
  funext m k
  show (c m k || c m k) = c m k
  cases c m k <;> rfl

/-- cutMax with zero (left identity for top): max(0-cut, c) = 0-cut.
    Wait — constCut 0 1 is "0 ≤ everything" = true.  max with always-true = c.
    But "max(0, c) = c" (numerically).  Cut: "max ≤ m/k" = "0 ≤ m/k AND c ≤ m/k"
    = "true AND c m k" = "c m k".  So max(0, c) = c. -/
theorem cutMax_zero_left (c : Nat → Nat → Bool) :
    cutMax (constCut 0 1) c = c := by
  funext m k
  show ((constCut 0 1) m k && c m k) = c m k
  rw [constCut_zero_always]
  cases c m k <;> rfl

/-- cutMin with zero: min(0, c) = 0 (= always true cut).
    "min ≤ m/k" = "0 ≤ m/k OR c ≤ m/k" = "true" = constCut 0 1. -/
theorem cutMin_zero_left (c : Nat → Nat → Bool) :
    cutMin (constCut 0 1) c = constCut 0 1 := by
  funext m k
  show ((constCut 0 1) m k || c m k) = constCut 0 1 m k
  rw [constCut_zero_always]
  cases c m k <;> rfl

end E213.Research.Real213CutSum
