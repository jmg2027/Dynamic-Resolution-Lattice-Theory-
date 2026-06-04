import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L5T

/-!
# Order-4 Monopoly at L6 ZSqrt[-2] (Type B, 32 units)

L6 = CD-doubling of L5. Units = (u, 0) ∪ (0, u) for u ∈ L5T_units.
Predicted distribution: {1 of order 1, 1 of order 2, 30 of order 4}.

Pinned ∅-axiom by direct decidable computation.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2

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

/-- L5T -1 lifted to L6T. -/
def L6T_minus_one : L6T := L6T_left L5T_minus_one

set_option maxHeartbeats 4000000 in
/-- ★★★ ORDER-4 MONOPOLY MECHANISM at L6: every L6T_right unit
    (lifted from L5T via CD doubling's "im axis") squares to -1.
    Same identity as L5T: (0, u)² = (-N(u), 0) = (-1, 0). -/
theorem L6T_right_squared_is_minus_one_first8 :
    ∀ u ∈ (L4T_units.map L5T_left),
    L6T_right u * L6T_right u = L6T_minus_one := by decide

set_option maxHeartbeats 4000000 in
/-- Same for L5T_right lifted. -/
theorem L6T_right_squared_is_minus_one_last8 :
    ∀ u ∈ (L4T_units.map L5T_right),
    L6T_right u * L6T_right u = L6T_minus_one := by decide

end E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2
