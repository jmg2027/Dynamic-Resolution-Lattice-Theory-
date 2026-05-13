import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Levels.Cayley

/-!
# Order-4 Monopoly at Type A L4 (Cayley octonion units = M_16)

Cayley = CD-double of Lipschitz = Type A L4 = 16 units (M_16 Moufang
loop = octonion unit basis).

Predicted distribution: {1 of order 1, 1 of order 2, 14 of order 4}.

This complements L5T_order_distribution (Type B L5) — both have the
same M_16 Moufang loop structure by the shift rule.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.Cayley

open E213.Lib.Math.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz

/-- Lipschitz zero. -/
def lip_zero : Lipschitz := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Cayley unit (u, 0). -/
def cay_left (u : Lipschitz) : Cayley := ⟨u, lip_zero⟩

/-- Cayley unit (0, u). -/
def cay_right (u : Lipschitz) : Cayley := ⟨lip_zero, u⟩

/-- 16 Cayley units = 8 left + 8 right. -/
def cay_units : List Cayley :=
  (lip_units.map cay_left) ++ (lip_units.map cay_right)

def cay_one : Cayley := cay_left lip_one
def cay_minus_one : Cayley := cay_left lip_minus_one

def cay_orderOf (u : Cayley) : Nat :=
  if u = cay_one then 1
  else if u * u = cay_one then 2
  else if u * u * u * u = cay_one then 4
  else 0

/-- ★ Octonion M_16 Order-4 Monopoly: distribution (1, 1, 14). -/
theorem cay_order_distribution :
    cay_units.countP (fun u => cay_orderOf u = 1) = 1 ∧
    cay_units.countP (fun u => cay_orderOf u = 2) = 1 ∧
    cay_units.countP (fun u => cay_orderOf u = 4) = 14 ∧
    cay_units.countP (fun u => cay_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 elements: 14 of 16 units. -/
theorem cay_order_4_count :
    cay_units.countP (fun u => cay_orderOf u = 4) = 14 :=
  cay_order_distribution.2.2.1

/-- ★★ Cayley "im axis" (0, u) units square to -1 — generic mechanism
    instance for the ZI tower at layer L4. -/
theorem cay_im_axis_squared :
    cay_right lip_unit_0 * cay_right lip_unit_0 = cay_minus_one ∧
    cay_right lip_unit_2 * cay_right lip_unit_2 = cay_minus_one ∧
    cay_right lip_unit_4 * cay_right lip_unit_4 = cay_minus_one ∧
    cay_right lip_unit_6 * cay_right lip_unit_6 = cay_minus_one := by decide

end E213.Lib.Math.CayleyDickson.Levels.Cayley
