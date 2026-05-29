import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

/-!
# `ZOmegaQuad` — CD-doubling of `ZOmegaDouble` (Type C L4)

Mechanical CD-doubling extension + Type C L4 order analysis.

ZOmegaQuad = CD-double of ZOmegaDouble = Type C L4 = 24 units.

Predicted distribution: {1, 1, 2, 18, 2} for orders (1, 2, 3, 4, 6).
M_24 Chein loop = M(Dic_3, 2) construction.

Order-4 monopoly: 18 = (24 − 6) = 6 (preserved from L3) + 12 (newly added).
Cyclotomic preservation: 4 (order 3 + 6) — exactly same as Type C L3.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble.ZOmegaDouble

structure ZOmegaQuad where
  re : ZOmegaDouble
  im : ZOmegaDouble
  deriving DecidableEq, Repr

namespace ZOmegaQuad

instance : Zero ZOmegaQuad := ⟨⟨0, 0⟩⟩

theorem ext {u v : ZOmegaQuad} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication.  Same formula, applied to the inner ZOmegaDouble. -/
def mul (u v : ZOmegaQuad) : ZOmegaQuad :=
  ⟨u.re * v.re - (ZOmegaDouble.conj v.im) * u.im,
    v.im * u.re + u.im * (ZOmegaDouble.conj v.re)⟩

instance : Mul ZOmegaQuad := ⟨mul⟩

def conj (u : ZOmegaQuad) : ZOmegaQuad :=
  ⟨ZOmegaDouble.conj u.re, -u.im⟩

def normSq (u : ZOmegaQuad) : Int :=
  ZOmegaDouble.normSq u.re + ZOmegaDouble.normSq u.im

end ZOmegaQuad

/-! ## Order distribution (Type C L4, M_24 Chein loop) -/

def zod_zero : ZOmegaDouble := ⟨0, 0⟩

def zoq_left (u : ZOmegaDouble) : ZOmegaQuad := ⟨u, zod_zero⟩
def zoq_right (u : ZOmegaDouble) : ZOmegaQuad := ⟨zod_zero, u⟩

/-- 24 ZOmegaQuad units = 12 left + 12 right. -/
def zoq_units : List ZOmegaQuad :=
  (zod_units.map zoq_left) ++ (zod_units.map zoq_right)

def zoq_one : ZOmegaQuad := zoq_left zod_one

def zoq_orderOf (u : ZOmegaQuad) : Nat :=
  if u = zoq_one then 1
  else if u * u = zoq_one then 2
  else if u * u * u = zoq_one then 3
  else if u * u * u * u = zoq_one then 4
  else if u * u * u * u * u * u = zoq_one then 6
  else 0

set_option maxHeartbeats 4000000 in
/-- ★ M_24 (Chein loop) order distribution: (1, 1, 2, 18, 2). -/
theorem zoq_order_distribution :
    zoq_units.countP (fun u => zoq_orderOf u = 1) = 1 ∧
    zoq_units.countP (fun u => zoq_orderOf u = 2) = 1 ∧
    zoq_units.countP (fun u => zoq_orderOf u = 3) = 2 ∧
    zoq_units.countP (fun u => zoq_orderOf u = 4) = 18 ∧
    zoq_units.countP (fun u => zoq_orderOf u = 6) = 2 ∧
    zoq_units.countP (fun u => zoq_orderOf u = 0) = 0 := by decide

/-- ★ Order-4 elements: 18 of 24 units. -/
theorem zoq_order_4_count :
    zoq_units.countP (fun u => zoq_orderOf u = 4) = 18 :=
  zoq_order_distribution.2.2.2.1

/-- ★ Cyclotomic-3,6 fossils preserved: still 4 elements (= L3 count). -/
theorem zoq_cyclotomic_preserved :
    zoq_units.countP (fun u => zoq_orderOf u = 3) +
      zoq_units.countP (fun u => zoq_orderOf u = 6) = 4 := by decide

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
