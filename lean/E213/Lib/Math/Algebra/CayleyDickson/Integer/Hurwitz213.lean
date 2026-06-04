/-!
# Hurwitz quaternion order — Type D base

24-unit binary tetrahedral group 2T = SL(2, F_3) as quaternion order.

Representation: 4-tuple of Int with **scaled-by-2 convention**:
  - actual element x = a + bi + cj + dk
  - stored as (2a, 2b, 2c, 2d) so all coordinates are integer
  - identity = (2, 0, 0, 0); negative identity = (-2, 0, 0, 0)
  - 8 Lipschitz units = ±2 in one coord, 0 in others
  - 16 half-integer units = (±1, ±1, ±1, ±1)
  - norm in scaled = a² + b² + c² + d²; unit ↔ scaled-norm = 4

Multiplication formula divides by 2 at end (always exact for Hurwitz units).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213

structure Hurwitz where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

instance : Zero Hurwitz := ⟨⟨0, 0, 0, 0⟩⟩

/-- Quaternion multiplication, divided by 2 (Int truncated division). -/
def mul (u v : Hurwitz) : Hurwitz :=
  ⟨ (u.a * v.a - u.b * v.b - u.c * v.c - u.d * v.d) / 2,
    (u.a * v.b + u.b * v.a + u.c * v.d - u.d * v.c) / 2,
    (u.a * v.c - u.b * v.d + u.c * v.a + u.d * v.b) / 2,
    (u.a * v.d + u.b * v.c - u.c * v.b + u.d * v.a) / 2 ⟩

instance : Mul Hurwitz := ⟨mul⟩

/-- Identity (= 1 in scaled rep). -/
def hur_one : Hurwitz := ⟨2, 0, 0, 0⟩
def hur_minus_one : Hurwitz := ⟨-2, 0, 0, 0⟩

/-- Scaled norm: a² + b² + c² + d². Unit ↔ = 4. -/
def normSq (u : Hurwitz) : Int :=
  u.a * u.a + u.b * u.b + u.c * u.c + u.d * u.d

/-- The 24 Hurwitz units in scaled rep. -/
def hur_units : List Hurwitz :=
  [-- 8 Lipschitz units (±2 in one coord)
   ⟨ 2, 0, 0, 0⟩, ⟨-2, 0, 0, 0⟩,
   ⟨ 0, 2, 0, 0⟩, ⟨ 0,-2, 0, 0⟩,
   ⟨ 0, 0, 2, 0⟩, ⟨ 0, 0,-2, 0⟩,
   ⟨ 0, 0, 0, 2⟩, ⟨ 0, 0, 0,-2⟩,
   -- 16 half-integer units (±1, ±1, ±1, ±1)
   ⟨ 1, 1, 1, 1⟩, ⟨ 1, 1, 1,-1⟩, ⟨ 1, 1,-1, 1⟩, ⟨ 1, 1,-1,-1⟩,
   ⟨ 1,-1, 1, 1⟩, ⟨ 1,-1, 1,-1⟩, ⟨ 1,-1,-1, 1⟩, ⟨ 1,-1,-1,-1⟩,
   ⟨-1, 1, 1, 1⟩, ⟨-1, 1, 1,-1⟩, ⟨-1, 1,-1, 1⟩, ⟨-1, 1,-1,-1⟩,
   ⟨-1,-1, 1, 1⟩, ⟨-1,-1, 1,-1⟩, ⟨-1,-1,-1, 1⟩, ⟨-1,-1,-1,-1⟩]

/-- All 24 units have scaled-norm 4 (the unit condition). -/
theorem hur_units_norm :
    hur_units.all (fun u => normSq u = 4) = true := by decide

/-- 24 elements in unit list. -/
theorem hur_units_count : hur_units.length = 24 := by decide

/-- Bounded order check up to 6 (max order in 2T). -/
def hur_orderOf (u : Hurwitz) : Nat :=
  if u = hur_one then 1
  else if u * u = hur_one then 2
  else if u * u * u = hur_one then 3
  else if u * u * u * u = hur_one then 4
  else if u * u * u * u * u * u = hur_one then 6
  else 0

set_option maxHeartbeats 4000000 in
/-- ★ Hurwitz unit group = 2T (binary tetrahedral) — order distribution
    (1, 1, 8, 6, 8) for orders (1, 2, 3, 4, 6).

    Type D base unit fingerprint as ∅-axiom theorem. -/
theorem hur_order_distribution :
    hur_units.countP (fun u => hur_orderOf u = 1) = 1 ∧
    hur_units.countP (fun u => hur_orderOf u = 2) = 1 ∧
    hur_units.countP (fun u => hur_orderOf u = 3) = 8 ∧
    hur_units.countP (fun u => hur_orderOf u = 4) = 6 ∧
    hur_units.countP (fun u => hur_orderOf u = 6) = 8 ∧
    hur_units.countP (fun u => hur_orderOf u = 0) = 0 := by decide

theorem hur_order_4_count :
    hur_units.countP (fun u => hur_orderOf u = 4) = 6 :=
  hur_order_distribution.2.2.2.1

/-- ★ Cyclotomic preservation at base: 16 elements of order 3 or 6
    (the 16 half-integer units, the η-cyclic structure). -/
theorem hur_cyclotomic_count :
    hur_units.countP (fun u => hur_orderOf u = 3) +
      hur_units.countP (fun u => hur_orderOf u = 6) = 16 := by decide

end E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213
