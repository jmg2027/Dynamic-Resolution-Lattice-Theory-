import E213.Meta.Algebra213.CDDouble
import E213.Meta.Algebra213.CDDoubleStar

/-!
# Theory.CDDouble — generic Order-4 Cayley–Dickson double mechanism

The Order-4 Monopoly micro-mechanism `(0, u)² = (-1, 0)` for unit
`u` formulated and proven generically over any `StarRing213` base.

Generalises the `L5T_right_squared_is_minus_one` and `L6T_right_*`
theorems (decide-based for finite cases) to a universal inductive
principle: ANY CDDouble of a star-ring with a unit `u` satisfying
`conj(u) · u = 1` will have `(0, u)² = (-1, 0)`.  Combined with
`(0, u)⁴ = ((-1, 0))² = (1, 0)`, every "lifted" element `(0, u)`
has order dividing 4.  For non-trivial rings (where `-1 ≠ 1`),
order is exactly 4.

This is the *generic version* of the Order-4 Monopoly law observed
empirically across all 4 base types (A, B, C, D) at every CD
doubling layer.

The companion `GenericLiftDemo` section below shows the
`cdd_lift_squared` mechanism applies through Lean's typeclass
inference to a *second* CD layer via the generic
`[CommStarRing213 α] : StarRing213 (CDDouble α)` instance —
no per-layer hand-written instance.


+ `Theory/CDDouble/GenericLiftDemo.lean`.
-/

open E213.Meta.Algebra213
open E213.Meta.Algebra213.CDDouble

namespace E213.Theory.CDDouble.UniversalOrder4

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
  · show (0 : α) * 0 + -(StarRing213.conj u * u) = -c
    rw [Ring213.zero_mul, h_unit, Ring213.zero_add]
  · show u * (0 : α) + u * StarRing213.conj 0 = 0
    rw [conj_zero, Ring213.mul_zero, Ring213.add_zero]

end E213.Theory.CDDouble.UniversalOrder4

namespace E213.Theory.CDDouble.GenericLiftDemo

open E213.Theory.CDDouble.UniversalOrder4

/-- ★ Sanity demo: `cdd_lift_squared` at *second* CD layer, derived
    purely via the generic `[CommStarRing213 α] : StarRing213
    (CDDouble α)` instance.

    Setup: take any `[CommStarRing213 α]`.  By the generic instance,
    `CDDouble α` is `StarRing213`.  By `cdd_lift_squared` on the
    abstract `StarRing213` level, every `(0, u) : CDDouble (CDDouble α)`
    where `conj u * u = c` satisfies `(0, u)² = (-c, 0)`.

    No per-layer instance written.  All inferred. -/
theorem cdd_lift_squared_at_layer2 {α : Type} [CommStarRing213 α]
    (u c : CDDouble α)
    (h_unit : StarRing213.conj u * u = c) :
    let v : CDDouble (CDDouble α) := ⟨0, u⟩
    (v * v).re = -c ∧ (v * v).im = 0 :=
  cdd_lift_squared u c h_unit

end E213.Theory.CDDouble.GenericLiftDemo
