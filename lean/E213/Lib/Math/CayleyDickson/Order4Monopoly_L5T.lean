import E213.Lib.Math.CayleyDickson.Order4Monopoly_L4T

/-!
# Order-4 Monopoly at L5 ZSqrt[-2] (Type B, 16 units)

L5 = CD-doubling of L4. Units are exactly {(u, 0)} ∪ {(0, u)} for u
ranging over L4T's 8 units, giving 16 total.

Predicted distribution by Order-4 Monopoly law (Rust-discovered):
  {1 of order 1, 1 of order 2, 14 of order 4}

Pinned ∅-axiom by direct decidable computation.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

/-- L4T zero (identity of additive structure). -/
def L4T_zero : L4T := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

/-- L5T unit (u, 0) for u ∈ L4T units. -/
def L5T_left (u : L4T) : L5T := ⟨u, L4T_zero⟩

/-- L5T unit (0, u) for u ∈ L4T units. -/
def L5T_right (u : L4T) : L5T := ⟨L4T_zero, u⟩

/-- The 16 units of L5T = 8 L4T-left units + 8 L4T-right units. -/
def L5T_units : List L5T :=
  (L4T_units.map L5T_left) ++ (L4T_units.map L5T_right)

def L5T_one : L5T := L5T_left L4T_one

/-- Bounded order check up to order 4. -/
def L5T_orderOf (u : L5T) : Nat :=
  if u = L5T_one then 1
  else if u * u = L5T_one then 2
  else if u * u * u * u = L5T_one then 4
  else 0

/-- ★ Full Order-4 Monopoly fingerprint at L5: distribution (1, 1, 14). -/
theorem L5T_order_distribution :
    L5T_units.countP (fun u => L5T_orderOf u = 1) = 1 ∧
    L5T_units.countP (fun u => L5T_orderOf u = 2) = 1 ∧
    L5T_units.countP (fun u => L5T_orderOf u = 4) = 14 ∧
    L5T_units.countP (fun u => L5T_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 elements count: 14 of 16 units. -/
theorem L5T_order_4_count :
    L5T_units.countP (fun u => L5T_orderOf u = 4) = 14 :=
  L5T_order_distribution.2.2.1

/-- L4T value -1 lifted as L5T (= ⟨L4T_minus_one, L4T_zero⟩). -/
def L5T_minus_one : L5T := L5T_left L4T_minus_one

/-- ★★★ ORDER-4 MONOPOLY (CORE): every L5T_right unit (lifted from L4T)
    squares to L5T_minus_one. This is the *mechanism* behind the order-4
    monopoly: CD doubling's new "im axis" elements satisfy x² = −1 by
    construction (since the doubling formula gives (0, u)·(0, u) =
    (−conj(u)·u, 0) = (−1, 0) when u is a unit). -/
theorem L5T_right_squared_is_minus_one :
    L5T_right L4T_unit_0 * L5T_right L4T_unit_0 = L5T_minus_one ∧
    L5T_right L4T_unit_1 * L5T_right L4T_unit_1 = L5T_minus_one ∧
    L5T_right L4T_unit_2 * L5T_right L4T_unit_2 = L5T_minus_one ∧
    L5T_right L4T_unit_3 * L5T_right L4T_unit_3 = L5T_minus_one ∧
    L5T_right L4T_unit_4 * L5T_right L4T_unit_4 = L5T_minus_one ∧
    L5T_right L4T_unit_5 * L5T_right L4T_unit_5 = L5T_minus_one ∧
    L5T_right L4T_unit_6 * L5T_right L4T_unit_6 = L5T_minus_one ∧
    L5T_right L4T_unit_7 * L5T_right L4T_unit_7 = L5T_minus_one := by decide

/-- ★ ORDER-4 MONOPOLY (consequence): every L5T_right unit has order 4. -/
theorem L5T_right_all_order_4 :
    L5T_orderOf (L5T_right L4T_unit_0) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_1) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_2) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_3) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_4) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_5) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_6) = 4 ∧
    L5T_orderOf (L5T_right L4T_unit_7) = 4 := by decide

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
