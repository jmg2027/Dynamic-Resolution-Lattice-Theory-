import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtMinus2Tower

/-!
# Order-4 Monopoly law — first ∅-axiom witness instance

Discovery (Rust probe,): for every CD doubling tower in the
213 corpus, the unit set's order distribution satisfies:

  base's cyclotomic substructure (order ≠ 4 elements) is *exactly
  preserved* across all CD doublings, and EVERY new element added per
  layer is of order 4.

This file pins the smallest non-trivial witness: ZSqrt[-2] L4 (Type B,
8 units). All 8 units enumerated, multiplications computed, individual
orders verified by `decide` (∅-axiom).

213-native: no external "Q_8" or "binary tetrahedral" naming. The
statement is purely "8 elements with these orders, by direct decidable
computation".
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt

-- 8 units of L4T (Type B at L4)
def L4T_unit_0 : L4T := ⟨⟨⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩  -- +1
def L4T_unit_1 : L4T := ⟨⟨⟨-1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩  -- -1
def L4T_unit_2 : L4T := ⟨⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
def L4T_unit_3 : L4T := ⟨⟨⟨0, 0⟩, ⟨-1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
def L4T_unit_4 : L4T := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨1, 0⟩, ⟨0, 0⟩⟩⟩
def L4T_unit_5 : L4T := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩⟩
def L4T_unit_6 : L4T := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨1, 0⟩⟩⟩
def L4T_unit_7 : L4T := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1, 0⟩⟩⟩

def L4T_one : L4T := L4T_unit_0
def L4T_minus_one : L4T := L4T_unit_1

/-- ★ Identity has order 1. -/
theorem L4T_unit_0_order_1 : L4T_unit_0 = L4T_one := by decide

/-- ★ −1 has order 2 (squares to identity). -/
theorem L4T_unit_1_order_2 : L4T_unit_1 * L4T_unit_1 = L4T_one := by decide

/-- ★ Each non-±1 unit has order 4 (squares to -1, fourth-power to 1). -/
theorem L4T_unit_2_order_4 :
    L4T_unit_2 * L4T_unit_2 = L4T_minus_one ∧
    L4T_unit_2 * L4T_unit_2 * (L4T_unit_2 * L4T_unit_2) = L4T_one := by decide

theorem L4T_unit_3_order_4 :
    L4T_unit_3 * L4T_unit_3 = L4T_minus_one ∧
    L4T_unit_3 * L4T_unit_3 * (L4T_unit_3 * L4T_unit_3) = L4T_one := by decide

theorem L4T_unit_4_order_4 :
    L4T_unit_4 * L4T_unit_4 = L4T_minus_one ∧
    L4T_unit_4 * L4T_unit_4 * (L4T_unit_4 * L4T_unit_4) = L4T_one := by decide

theorem L4T_unit_5_order_4 :
    L4T_unit_5 * L4T_unit_5 = L4T_minus_one ∧
    L4T_unit_5 * L4T_unit_5 * (L4T_unit_5 * L4T_unit_5) = L4T_one := by decide

theorem L4T_unit_6_order_4 :
    L4T_unit_6 * L4T_unit_6 = L4T_minus_one ∧
    L4T_unit_6 * L4T_unit_6 * (L4T_unit_6 * L4T_unit_6) = L4T_one := by decide

theorem L4T_unit_7_order_4 :
    L4T_unit_7 * L4T_unit_7 = L4T_minus_one ∧
    L4T_unit_7 * L4T_unit_7 * (L4T_unit_7 * L4T_unit_7) = L4T_one := by decide

/-- Full unit list. -/
def L4T_units : List L4T :=
  [L4T_unit_0, L4T_unit_1, L4T_unit_2, L4T_unit_3,
   L4T_unit_4, L4T_unit_5, L4T_unit_6, L4T_unit_7]

/-- Bounded order: 1, 2, 4, or 0 (not in those). -/
def L4T_orderOf (u : L4T) : Nat :=
  if u = L4T_one then 1
  else if u * u = L4T_one then 2
  else if u * u * u * u = L4T_one then 4
  else 0

/-- ★ Order distribution of L4T units: (1, 1, 6) for orders (1, 2, 4). -/
theorem L4T_order_distribution :
    L4T_units.countP (fun u => L4T_orderOf u = 1) = 1 ∧
    L4T_units.countP (fun u => L4T_orderOf u = 2) = 1 ∧
    L4T_units.countP (fun u => L4T_orderOf u = 4) = 6 ∧
    L4T_units.countP (fun u => L4T_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 Monopoly at L4 (Type B): exactly 6 elements of order 4
    out of 8 units; only ±1 have other orders. -/
theorem L4T_order_4_count : L4T_units.countP (fun u => L4T_orderOf u = 4) = 6 :=
  L4T_order_distribution.2.2.1

end E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2
