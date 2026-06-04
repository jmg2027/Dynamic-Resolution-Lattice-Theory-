import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble

/-!
# Order-4 Monopoly at Type A L3 (Lipschitz quaternion units = Q_8)

Lipschitz = CD-double of ZI = Type A L3 = 8 units (Q_8 structure).
Predicted distribution: {1 of order 1, 1 of order 2, 6 of order 4}.

This complements Order4Monopoly_L4T which proves the same distribution
for Type B L4 (ZSqrt[-2] tower). By the shift rule discovered in this
session, both have the SAME unit Moufang loop structure (Q_8).

Pinned ∅-axiom by direct decidable computation on Lipschitz units.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI

/-- 8 Lipschitz units (Q_8 elements). -/
def lip_unit_0 : Lipschitz := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩    -- +1
def lip_unit_1 : Lipschitz := ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩   -- -1
def lip_unit_2 : Lipschitz := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩    -- +i
def lip_unit_3 : Lipschitz := ⟨⟨0, -1⟩, ⟨0, 0⟩⟩   -- -i
def lip_unit_4 : Lipschitz := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩    -- +j
def lip_unit_5 : Lipschitz := ⟨⟨0, 0⟩, ⟨-1, 0⟩⟩   -- -j
def lip_unit_6 : Lipschitz := ⟨⟨0, 0⟩, ⟨0, 1⟩⟩    -- +k = i*j
def lip_unit_7 : Lipschitz := ⟨⟨0, 0⟩, ⟨0, -1⟩⟩   -- -k

def lip_one : Lipschitz := lip_unit_0
def lip_minus_one : Lipschitz := lip_unit_1

def lip_units : List Lipschitz :=
  [lip_unit_0, lip_unit_1, lip_unit_2, lip_unit_3,
   lip_unit_4, lip_unit_5, lip_unit_6, lip_unit_7]

/-- Bounded order check: 1, 2, 4, or 0. -/
def lip_orderOf (u : Lipschitz) : Nat :=
  if u = lip_one then 1
  else if u * u = lip_one then 2
  else if u * u * u * u = lip_one then 4
  else 0

/-- ★ Q_8 Order-4 Monopoly fingerprint: distribution (1, 1, 6). -/
theorem lip_order_distribution :
    lip_units.countP (fun u => lip_orderOf u = 1) = 1 ∧
    lip_units.countP (fun u => lip_orderOf u = 2) = 1 ∧
    lip_units.countP (fun u => lip_orderOf u = 4) = 6 ∧
    lip_units.countP (fun u => lip_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 elements: 6 of 8 units (matches Type B L4). -/
theorem lip_order_4_count :
    lip_units.countP (fun u => lip_orderOf u = 4) = 6 :=
  lip_order_distribution.2.2.1

/-- ★★ Lipschitz "im axis" (0, u) units square to -1 — same micro-mechanism
    as L5T at Type B. Verifies Order-4 Monopoly for ZI base side. -/
theorem lip_im_axis_squared :
    lip_unit_4 * lip_unit_4 = lip_minus_one ∧
    lip_unit_5 * lip_unit_5 = lip_minus_one ∧
    lip_unit_6 * lip_unit_6 = lip_minus_one ∧
    lip_unit_7 * lip_unit_7 = lip_minus_one := by decide

end E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
