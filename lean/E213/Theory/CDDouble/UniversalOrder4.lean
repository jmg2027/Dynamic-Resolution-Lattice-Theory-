import E213.Theory.Internal.Algebra213CDDouble

/-!
# Theory.CDDouble.UniversalOrder4 — generic Order-4 Monopoly mechanism

The Order-4 Monopoly micro-mechanism (0, u)² = (-1, 0) for unit u
formulated and proven generically over any StarRing213 base.

This generalizes the L5T_right_squared_is_minus_one and L6T_right_*
theorems (which are decide-based for finite cases) to a universal
inductive principle: ANY CDDouble of a star-ring with a unit u
satisfying conj(u)·u = 1 will have (0, u)² = (-1, 0).

Combined with (0, u)⁴ = ((-1, 0))² = (1, 0), this establishes that
every "lifted" element (0, u) has order dividing 4. For non-trivial
rings (where -1 ≠ 1), order is exactly 4.

This is the *generic version* of the Order-4 Monopoly law observed
empirically across all 4 base types (A, B, C, D) at every CD doubling
layer.
-/

namespace E213.Theory.CDDouble.UniversalOrder4

open E213.Theory.Internal.Algebra213
open E213.Theory.Internal.Algebra213.CDDouble

variable {α : Type} [StarRing213 α]

/-- ★ Helper: `conj 0 = 0` for any StarRing213. -/
theorem conj_zero : StarRing213.conj (0 : α) = 0 := by
  have h : StarRing213.conj (0 : α) = StarRing213.conj (0 : α) + StarRing213.conj (0 : α) := by
    have z : (0 : α) + 0 = 0 := Ring213.add_zero 0
    calc StarRing213.conj (0 : α)
        = StarRing213.conj ((0 : α) + 0) := by rw [z]
      _ = StarRing213.conj (0 : α) + StarRing213.conj (0 : α) := StarRing213.conj_add (0 : α) 0
  have hneg : -StarRing213.conj (0 : α) + StarRing213.conj (0 : α) = 0 :=
    Ring213.add_left_neg (StarRing213.conj (0 : α))
  have h2 : (0 : α) = StarRing213.conj (0 : α) := by
    calc (0 : α) = -StarRing213.conj (0 : α) + StarRing213.conj (0 : α) := hneg.symm
      _ = -StarRing213.conj (0 : α)
            + (StarRing213.conj (0 : α) + StarRing213.conj (0 : α)) := by rw [← h]
      _ = (-StarRing213.conj (0 : α) + StarRing213.conj (0 : α))
            + StarRing213.conj (0 : α) := (Ring213.add_assoc _ _ _).symm
      _ = 0 + StarRing213.conj (0 : α) := by rw [hneg]
      _ = StarRing213.conj (0 : α) + 0 := Ring213.add_comm _ _
      _ = StarRing213.conj (0 : α) := Ring213.add_zero _
  exact h2.symm

/-- ★★★ ORDER-4 MONOPOLY UNIVERSAL MECHANISM:

    For any StarRing213 base α with element u satisfying
    `conj(u) * u = c`, the CDDouble element `(0, u)` squared equals
    `(-c, 0)`. This is the *generic mechanism* causing Order-4 Monopoly:
    when c = 1 (u is a unit), (0, u)² = (-1, 0), giving order 4. -/
theorem cdd_lift_squared (u c : α) (h_unit : StarRing213.conj u * u = c) :
    let v : CDDouble α := ⟨0, u⟩
    (v * v).re = -c ∧ (v * v).im = 0 := by
  refine ⟨?_, ?_⟩
  · -- (v*v).re = 0 * 0 + -(conj u * u) = 0 + -c = -c
    show (0 : α) * 0 + -(StarRing213.conj u * u) = -c
    rw [Ring213.zero_mul, h_unit, Ring213.zero_add]
  · -- (v*v).im = u * 0 + u * conj 0 = 0 + 0 = 0
    show u * (0 : α) + u * StarRing213.conj 0 = 0
    rw [conj_zero, Ring213.mul_zero, Ring213.add_zero]

end E213.Theory.CDDouble.UniversalOrder4
