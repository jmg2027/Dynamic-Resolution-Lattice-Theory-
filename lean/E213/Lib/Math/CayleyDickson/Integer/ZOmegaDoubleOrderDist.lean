import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

/-!
# Order distribution at Type C L3 (ZOmegaDouble = Dic_3, 12 units)

ZOmegaDouble = CD-double of ZOmega = Type C L3 = 12 units.

This is the FIRST layer where Order-4 Monopoly's rule is *complicated*:
the base ZOmega already has order-3 and order-6 elements (cyclotomic
preservation), so the new layer's order distribution has 5 different
orders, not just {1, 2, 4}.

Predicted distribution: {1, 1, 2, 6, 2} for orders (1, 2, 3, 4, 6).
This is the Dic_3 (binary dihedral / dicyclic) group's order signature.

Critical: the order-4 count = 6 is exactly the number of NEW elements
added by this CD doubling step (= |ZOmega units| = 6). The original
ZOmega's 6 units (orders 1, 2, 3, 6) are PRESERVED at the "left"
side; the new 6 units at "right" side ALL have order 4. This is the
Order-4 Monopoly law's manifestation when base has cyclotomic structure.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

/-- 6 ZOmega units. -/
def zo_units : List ZOmega :=
  [⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]

def zod_left (u : ZOmega) : ZOmegaDouble := ⟨u, 0⟩
def zod_right (u : ZOmega) : ZOmegaDouble := ⟨0, u⟩

/-- 12 ZOmegaDouble units = 6 left + 6 right. -/
def zod_units : List ZOmegaDouble :=
  (zo_units.map zod_left) ++ (zo_units.map zod_right)

def zod_one : ZOmegaDouble := zod_left ⟨1, 0⟩

/-- Bounded order check up to 6. -/
def zod_orderOf (u : ZOmegaDouble) : Nat :=
  if u = zod_one then 1
  else if u * u = zod_one then 2
  else if u * u * u = zod_one then 3
  else if u * u * u * u = zod_one then 4
  else if u * u * u * u * u * u = zod_one then 6
  else 0

/-- ★ Dic_3 order distribution (Type C L3, 12 units): (1, 1, 2, 6, 2). -/
theorem zod_order_distribution :
    zod_units.countP (fun u => zod_orderOf u = 1) = 1 ∧
    zod_units.countP (fun u => zod_orderOf u = 2) = 1 ∧
    zod_units.countP (fun u => zod_orderOf u = 3) = 2 ∧
    zod_units.countP (fun u => zod_orderOf u = 4) = 6 ∧
    zod_units.countP (fun u => zod_orderOf u = 6) = 2 ∧
    zod_units.countP (fun u => zod_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 elements: exactly 6 of 12 units (= |zo_units|, NEW
    elements added by CD doubling). The other 6 are PRESERVED from
    ZOmega base (orders 1, 2, 3, 3, 6, 6). -/
theorem zod_order_4_count :
    zod_units.countP (fun u => zod_orderOf u = 4) = 6 :=
  zod_order_distribution.2.2.2.1

/-- ★ Cyclotomic preservation: order-3 + order-6 count = base unit
    non-trivial cyclotomic count = 4 (from ZOmega's ω, ω², -ω, -ω²). -/
theorem zod_cyclotomic_preserved :
    zod_units.countP (fun u => zod_orderOf u = 3) +
      zod_units.countP (fun u => zod_orderOf u = 6) = 4 := by decide

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
