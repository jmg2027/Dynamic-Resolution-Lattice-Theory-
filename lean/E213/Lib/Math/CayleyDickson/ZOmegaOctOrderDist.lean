import E213.Lib.Math.CayleyDickson.ZOmegaQuadOrderDist
import E213.Lib.Math.CayleyDickson.ZOmegaOct

/-!
# Order distribution at Type C L5 (ZOmegaOct, 48 units, first past-Moufang)

ZOmegaOct = CD-double of ZOmegaQuad = Type C L5 = 48 units.
This is the FIRST PAST-MOUFANG layer for Type C (Mou fail rate ≈ 21.9%).

Distribution: {1, 1, 2, 42, 2} for orders (1, 2, 3, 4, 6).
Cyclotomic preservation continues: 4 elements of order 3 or 6.
Order-4 increment: 42 − 18 = 24 = base unit count |zoq_units|.
-/

namespace E213.Lib.Math.CayleyDickson.ZOmegaOct

open E213.Lib.Math.CayleyDickson.ZOmegaQuad
open E213.Lib.Math.CayleyDickson.ZOmegaQuad.ZOmegaQuad

def zoq_zero : ZOmegaQuad := ⟨zod_zero, zod_zero⟩

def zooct_left (u : ZOmegaQuad) : ZOmegaOct := ⟨u, zoq_zero⟩
def zooct_right (u : ZOmegaQuad) : ZOmegaOct := ⟨zoq_zero, u⟩

/-- 48 ZOmegaOct units = 24 left + 24 right. -/
def zooct_units : List ZOmegaOct :=
  (zoq_units.map zooct_left) ++ (zoq_units.map zooct_right)

def zooct_one : ZOmegaOct := zooct_left zoq_one

def zooct_orderOf (u : ZOmegaOct) : Nat :=
  if u = zooct_one then 1
  else if u * u = zooct_one then 2
  else if u * u * u = zooct_one then 3
  else if u * u * u * u = zooct_one then 4
  else if u * u * u * u * u * u = zooct_one then 6
  else 0

set_option maxHeartbeats 8000000 in
/-- ★ Type C L5 = first past-Moufang layer order distribution.
    (1, 1, 2, 42, 2) — Order-4 Monopoly persists past Moufang failure. -/
theorem zooct_order_distribution :
    zooct_units.countP (fun u => zooct_orderOf u = 1) = 1 ∧
    zooct_units.countP (fun u => zooct_orderOf u = 2) = 1 ∧
    zooct_units.countP (fun u => zooct_orderOf u = 3) = 2 ∧
    zooct_units.countP (fun u => zooct_orderOf u = 4) = 42 ∧
    zooct_units.countP (fun u => zooct_orderOf u = 6) = 2 ∧
    zooct_units.countP (fun u => zooct_orderOf u = 0) = 0 := by decide

theorem zooct_order_4_count :
    zooct_units.countP (fun u => zooct_orderOf u = 4) = 42 :=
  zooct_order_distribution.2.2.2.1

set_option maxHeartbeats 8000000 in
/-- ★ Cyclotomic preservation continues even past Moufang. -/
theorem zooct_cyclotomic_preserved :
    zooct_units.countP (fun u => zooct_orderOf u = 3) +
      zooct_units.countP (fun u => zooct_orderOf u = 6) = 4 := by decide

end E213.Lib.Math.CayleyDickson.ZOmegaOct
