import E213.Lib.Math.CayleyDickson.Order4Monopoly_L5T

/-!
# Order-4 Monopoly at L6 ZSqrt[-2] (Type B, 32 units)

L6 = CD-doubling of L5. Units = (u, 0) ∪ (0, u) for u ∈ L5T_units.
Predicted distribution: {1 of order 1, 1 of order 2, 30 of order 4}.

Pinned ∅-axiom by direct decidable computation.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

def L5T_zero : L5T := ⟨L4T_zero, L4T_zero⟩

def L6T_left (u : L5T) : L6T := ⟨u, L5T_zero⟩
def L6T_right (u : L5T) : L6T := ⟨L5T_zero, u⟩

def L6T_units : List L6T :=
  (L5T_units.map L6T_left) ++ (L5T_units.map L6T_right)

def L6T_one : L6T := L6T_left L5T_one

def L6T_orderOf (u : L6T) : Nat :=
  if u = L6T_one then 1
  else if u * u = L6T_one then 2
  else if u * u * u * u = L6T_one then 4
  else 0

set_option maxHeartbeats 4000000 in
/-- ★ Full Order-4 Monopoly fingerprint at L6: distribution (1, 1, 30). -/
theorem L6T_order_distribution :
    L6T_units.countP (fun u => L6T_orderOf u = 1) = 1 ∧
    L6T_units.countP (fun u => L6T_orderOf u = 2) = 1 ∧
    L6T_units.countP (fun u => L6T_orderOf u = 4) = 30 ∧
    L6T_units.countP (fun u => L6T_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 elements count: 30 of 32 units. -/
theorem L6T_order_4_count :
    L6T_units.countP (fun u => L6T_orderOf u = 4) = 30 :=
  L6T_order_distribution.2.2.1

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
