import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Meta.Int213.Core

/-!
# `ZOmegaDouble` — CD-doubling of Eisenstein integers (Type C L3)

Mechanical CD-doubling construction + Type C L3 order analysis
(consolidated 2026-05-18; previously split as `ZOmegaDouble.lean`
+ `ZOmegaDoubleOrderDist.lean`).

ZOmegaDouble = CD-double of ZOmega = Type C L3 = 12 units.  This
is the FIRST layer where Order-4 Monopoly's rule is non-trivial:
the base ZOmega already has order-3 and order-6 elements
(cyclotomic preservation), so the new layer's order distribution
has 5 different orders (1, 2, 3, 4, 6) — not just {1, 2, 4}.

Predicted distribution: {1, 1, 2, 6, 2} = Dic_3 (binary dihedral)
signature.  Critical: the order-4 count = 6 = NEW elements from CD
doubling.  Original 6 ZOmega units (orders 1, 2, 3, 6) PRESERVED
at "left" side; new 6 units at "right" side ALL have order 4 —
manifestation of Order-4 Monopoly when base has cyclotomic structure.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

-- Add/Neg for ZOmega (componentwise on Int)
namespace _root_.E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

instance : Add ZOmega := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg ZOmega := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub ZOmega := ⟨fun u v => u + (-v)⟩

end _root_.E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

structure ZOmegaDouble where
  re : ZOmega
  im : ZOmega
  deriving DecidableEq, Repr

namespace ZOmegaDouble

instance : Zero ZOmegaDouble := ⟨⟨0, 0⟩⟩

theorem ext {u v : ZOmegaDouble} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication: `(a, b)·(c, d) = (a·c - conj(d)·b, d·a + b·conj(c))`. -/
def mul (u v : ZOmegaDouble) : ZOmegaDouble :=
  ⟨u.re * v.re - (ZOmega.conj v.im) * u.im,
    v.im * u.re + u.im * (ZOmega.conj v.re)⟩

instance : Mul ZOmegaDouble := ⟨mul⟩

/-- CD conjugation. -/
def conj (u : ZOmegaDouble) : ZOmegaDouble :=
  ⟨ZOmega.conj u.re, -u.im⟩

/-- Norm = sum of inner Eisenstein norms. -/
def normSq (u : ZOmegaDouble) : Int :=
  ZOmega.normSq u.re + ZOmega.normSq u.im

-- Basis elements
def e1 : ZOmegaDouble := ⟨⟨1, 0⟩, 0⟩       -- real unit
def e2 : ZOmegaDouble := ⟨⟨0, 1⟩, 0⟩       -- ω axis
def e3 : ZOmegaDouble := ⟨0, ⟨1, 0⟩⟩       -- j-like
def e4 : ZOmegaDouble := ⟨0, ⟨0, 1⟩⟩       -- ωj-like

end ZOmegaDouble

/-! ## Order distribution (Type C L3, Dic_3 signature) -/

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
    elements from CD doubling). Other 6 PRESERVED from ZOmega base. -/
theorem zod_order_4_count :
    zod_units.countP (fun u => zod_orderOf u = 4) = 6 :=
  zod_order_distribution.2.2.2.1

/-- ★ Cyclotomic preservation: order-3 + order-6 = 4 (from ZOmega's
    ω, ω², -ω, -ω²). -/
theorem zod_cyclotomic_preserved :
    zod_units.countP (fun u => zod_orderOf u = 3) +
      zod_units.countP (fun u => zod_orderOf u = 6) = 4 := by decide

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
