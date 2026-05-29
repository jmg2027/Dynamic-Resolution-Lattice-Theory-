import E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad

/-!
# `ZOmegaOct` — CD doubling of `ZOmegaQuad` (Type C L5, first past-Moufang)

16-dim algebra over Eisenstein base + order analysis at 48 units.

Type C L5 is the FIRST PAST-MOUFANG layer for Type C
(Moufang failure rate ≈ 21.9%).  Distribution: {1, 1, 2, 42, 2}
for orders (1, 2, 3, 4, 6); Order-4 Monopoly persists past Moufang
failure.  Cyclotomic preservation continues: 4 elements of order
3 or 6.  Order-4 increment: 42 − 18 = 24 = base |zoq_units|.

 + `ZOmegaOctOrderDist.lean`.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad.ZOmegaQuad

structure ZOmegaOct where
  re : ZOmegaQuad
  im : ZOmegaQuad
  deriving DecidableEq, Repr

namespace ZOmegaOct

instance : Zero ZOmegaOct := ⟨⟨0, 0⟩⟩

theorem ext {u v : ZOmegaOct} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

def mul (u v : ZOmegaOct) : ZOmegaOct :=
  ⟨u.re * v.re - (ZOmegaQuad.conj v.im) * u.im,
    v.im * u.re + u.im * (ZOmegaQuad.conj v.re)⟩

instance : Mul ZOmegaOct := ⟨mul⟩

def conj (u : ZOmegaOct) : ZOmegaOct :=
  ⟨ZOmegaQuad.conj u.re, -u.im⟩

def normSq (u : ZOmegaOct) : Int :=
  ZOmegaQuad.normSq u.re + ZOmegaQuad.normSq u.im

end ZOmegaOct

/-! ## Order distribution (Type C L5, first past-Moufang) -/

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

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct
