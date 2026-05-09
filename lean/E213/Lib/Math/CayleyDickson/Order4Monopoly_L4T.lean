import E213.Lib.Math.CayleyDickson.ZSqrtMinus2Tower

/-!
# Order-4 Monopoly law — first ∅-axiom witness instance

Discovery (Rust probe, 2026-05-09): for every CD doubling tower in the
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

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

open E213.Lib.Math.CayleyDickson.ZSqrt

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

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
