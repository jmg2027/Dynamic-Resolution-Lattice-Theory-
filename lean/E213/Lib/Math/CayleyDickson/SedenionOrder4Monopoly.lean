import E213.Lib.Math.CayleyDickson.CayleyOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Sedenion

/-!
# Order-4 Monopoly at Type A L5 (Sedenion units, first Moufang-fail layer)

Sedenion = CD-double of Cayley = Type A L5 = 32 units.

Predicted distribution: {1, 1, 30} for orders (1, 2, 4).

This is the FIRST PAST-MOUFANG layer for Type A — alt-L still holds
on basis units (per Rust probe data: alt-L = 0/1024) but Moufang
identity fails on 21/128 of triples.

Same {1, 1, 30} distribution as L6T (Type B L6) by SHIFT RULE.

This module pins the distribution ∅-axiom on Sedenion's 32 units;
verifies Order-4 Monopoly persists at Type A's first past-Moufang.
-/

namespace E213.Lib.Math.CayleyDickson.Sedenion

open E213.Lib.Math.CayleyDickson.Cayley

/-- Cayley zero. -/
def cay_zero : Cayley := ⟨lip_zero, lip_zero⟩

/-- Sedenion unit (u, 0) lifted from Cayley. -/
def sed_left (u : Cayley) : Sedenion := ⟨u, cay_zero⟩

/-- Sedenion unit (0, u) — the new "im axis" at L5. -/
def sed_right (u : Cayley) : Sedenion := ⟨cay_zero, u⟩

/-- 32 Sedenion units = 16 left + 16 right. -/
def sed_units : List Sedenion :=
  (cay_units.map sed_left) ++ (cay_units.map sed_right)

def sed_one : Sedenion := sed_left cay_one
def sed_minus_one : Sedenion := sed_left cay_minus_one

def sed_orderOf (u : Sedenion) : Nat :=
  if u = sed_one then 1
  else if u * u = sed_one then 2
  else if u * u * u * u = sed_one then 4
  else 0

set_option maxHeartbeats 4000000 in
/-- ★ Sedenion Order-4 Monopoly: distribution (1, 1, 30) preserved at
    first past-Moufang layer (Type A L5).  Same as Type B L6.

    NOTE: This proves that even after Moufang fails (21/128 triples),
    Order-4 Monopoly STILL holds — every new element has order 4.
    The two laws are independent: Moufang can break while Order-4
    Monopoly persists. -/
theorem sed_order_distribution :
    sed_units.countP (fun u => sed_orderOf u = 1) = 1 ∧
    sed_units.countP (fun u => sed_orderOf u = 2) = 1 ∧
    sed_units.countP (fun u => sed_orderOf u = 4) = 30 ∧
    sed_units.countP (fun u => sed_orderOf u = 0) = 0 := by decide

theorem sed_order_4_count :
    sed_units.countP (fun u => sed_orderOf u = 4) = 30 :=
  sed_order_distribution.2.2.1

end E213.Lib.Math.CayleyDickson.Sedenion
