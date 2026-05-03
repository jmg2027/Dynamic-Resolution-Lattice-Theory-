import E213.Math.Real213.Core
import E213.Math.Real213.CutMaxMin
import E213.Math.Real213.CutPoset

/-!
# Research.Real213CutAlgebraic: algebraic properties of cut operations

Lattice properties of cutMax, cutMin + cut zero/one properties.
-/

namespace E213.Math.Real213.CutAlgebraic

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutMaxMin (cutMax cutMin)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutPoset (cutEq)

/-- constCut 0 1 always true ("0 ≤ everything"). -/
theorem constCut_zero_always (m k : Nat) : constCut 0 1 m k = true := by
  show decide (0 * k ≤ 1 * m) = true
  rw [Nat.zero_mul]
  exact decide_eq_true (Nat.zero_le _)

/-- cutMax idempotent pointwise (PURE). -/
theorem cutMax_idempotent_at (c : Nat → Nat → Bool) (m k : Nat) :
    cutMax c c m k = c m k := by
  show (c m k && c m k) = c m k
  cases c m k <;> rfl

/-- cutMax idempotent: max(c, c) ≡ c (cutEq, PURE). -/
theorem cutMax_idempotent (c : Nat → Nat → Bool) :
    cutEq (cutMax c c) c :=
  cutMax_idempotent_at c

/-- cutMin idempotent pointwise (PURE). -/
theorem cutMin_idempotent_at (c : Nat → Nat → Bool) (m k : Nat) :
    cutMin c c m k = c m k := by
  show (c m k || c m k) = c m k
  cases c m k <;> rfl

/-- cutMin idempotent (cutEq, PURE). -/
theorem cutMin_idempotent (c : Nat → Nat → Bool) :
    cutEq (cutMin c c) c :=
  cutMin_idempotent_at c

/-- cutMax with zero (left identity for top): max(0-cut, c) = 0-cut.
    Wait — constCut 0 1 is "0 ≤ everything" = true.  max with always-true = c.
    But "max(0, c) = c" (numerically).  Cut: "max ≤ m/k" = "0 ≤ m/k AND c ≤ m/k"
    = "true AND c m k" = "c m k".  So max(0, c) = c. -/
theorem cutMax_zero_left_at (c : Nat → Nat → Bool) (m k : Nat) :
    cutMax (constCut 0 1) c m k = c m k := by
  show ((constCut 0 1) m k && c m k) = c m k
  rw [constCut_zero_always]
  cases c m k <;> rfl

theorem cutMax_zero_left (c : Nat → Nat → Bool) :
    cutEq (cutMax (constCut 0 1) c) c :=
  cutMax_zero_left_at c

theorem cutMin_zero_left_at (c : Nat → Nat → Bool) (m k : Nat) :
    cutMin (constCut 0 1) c m k = constCut 0 1 m k := by
  show ((constCut 0 1) m k || c m k) = constCut 0 1 m k
  rw [constCut_zero_always]
  cases c m k <;> rfl

/-- cutMin with zero ≡ 0 (cutEq, PURE). -/
theorem cutMin_zero_left (c : Nat → Nat → Bool) :
    cutEq (cutMin (constCut 0 1) c) (constCut 0 1) :=
  cutMin_zero_left_at c

theorem cutMax_distrib_cutMin_at (cx cy cz : Nat → Nat → Bool) (m k : Nat) :
    cutMax cx (cutMin cy cz) m k
    = cutMin (cutMax cx cy) (cutMax cx cz) m k := by
  show (cx m k && (cy m k || cz m k))
     = ((cx m k && cy m k) || (cx m k && cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

theorem cutMax_distrib_cutMin (cx cy cz : Nat → Nat → Bool) :
    cutEq
      (cutMax cx (cutMin cy cz))
      (cutMin (cutMax cx cy) (cutMax cx cz)) :=
  cutMax_distrib_cutMin_at cx cy cz

theorem cutMin_distrib_cutMax_at (cx cy cz : Nat → Nat → Bool) (m k : Nat) :
    cutMin cx (cutMax cy cz) m k
    = cutMax (cutMin cx cy) (cutMin cx cz) m k := by
  show (cx m k || (cy m k && cz m k))
     = ((cx m k || cy m k) && (cx m k || cz m k))
  cases cx m k <;> cases cy m k <;> cases cz m k <;> rfl

theorem cutMin_distrib_cutMax (cx cy cz : Nat → Nat → Bool) :
    cutEq
      (cutMin cx (cutMax cy cz))
      (cutMax (cutMin cx cy) (cutMin cx cz)) :=
  cutMin_distrib_cutMax_at cx cy cz

theorem cutMax_absorb_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMax cx (cutMin cx cy) m k = cx m k := by
  show (cx m k && (cx m k || cy m k)) = cx m k
  cases cx m k <;> cases cy m k <;> rfl

theorem cutMax_absorb (cx cy : Nat → Nat → Bool) :
    cutEq (cutMax cx (cutMin cx cy)) cx :=
  cutMax_absorb_at cx cy

theorem cutMin_absorb_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutMin cx (cutMax cx cy) m k = cx m k := by
  show (cx m k || (cx m k && cy m k)) = cx m k
  cases cx m k <;> cases cy m k <;> rfl

theorem cutMin_absorb (cx cy : Nat → Nat → Bool) :
    cutEq (cutMin cx (cutMax cx cy)) cx :=
  cutMin_absorb_at cx cy

end E213.Math.Real213.CutAlgebraic
