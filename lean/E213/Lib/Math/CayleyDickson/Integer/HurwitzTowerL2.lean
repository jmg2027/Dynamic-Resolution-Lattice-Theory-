import E213.Lib.Math.CayleyDickson.Integer.HurwitzTowerL1
/-!
# Type D tower — Hurwitz CD-doubling at L2

Extends `HurwitzTowerL1` (HurwitzL2 = 48 units) to **HurwitzL3 =
HurwitzL2 × HurwitzL2 = 96 units**:

  · L0 (Hurwitz):  24 units (2T binary tetrahedral)
  · L1 (HurwitzL2): 48 units
  · **L2 (HurwitzL3): 96 units** (this file)

CD-doubling pattern uniform; Type D tower extends in lockstep with
Types A/B/C.  Full Order-N distribution at L2 exceeds `decide`
budget; structural shell only.

All declarations PURE.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.HurwitzTower

open E213.Lib.Math.CayleyDickson.Integer.Hurwitz213 (Hurwitz)

/-! ## §1 — HurwitzL3 = HurwitzL2 × HurwitzL2 -/

/-- HurwitzL3 = CD-doubling of HurwitzL2. -/
structure HurwitzL3 where
  re : HurwitzL2
  im : HurwitzL2
  deriving DecidableEq, Repr

namespace HurwitzL3

instance : Zero HurwitzL3 := ⟨⟨0, 0⟩⟩

/-- Componentwise HurwitzL2 addition (HurwitzL2 lacks Add). -/
def hl2Add (u v : HurwitzL2) : HurwitzL2 :=
  ⟨HurwitzL2.hurAdd u.re v.re, HurwitzL2.hurAdd u.im v.im⟩

/-- Componentwise HurwitzL2 negation. -/
def hl2Neg (u : HurwitzL2) : HurwitzL2 :=
  ⟨HurwitzL2.hurNeg u.re, HurwitzL2.hurNeg u.im⟩

/-- Componentwise HurwitzL2 subtraction. -/
def hl2Sub (u v : HurwitzL2) : HurwitzL2 := hl2Add u (hl2Neg v)

/-- CD-multiplication at L3 using HurwitzL2 ops. -/
def mul (u v : HurwitzL3) : HurwitzL3 :=
  ⟨hl2Sub (u.re * v.re) ((HurwitzL2.conj v.im) * u.im),
    hl2Add (v.im * u.re) (u.im * (HurwitzL2.conj v.re))⟩

instance : Mul HurwitzL3 := ⟨mul⟩

/-- HurwitzL3 norm-squared. -/
def normSq (u : HurwitzL3) : Int :=
  HurwitzL2.normSq u.re + HurwitzL2.normSq u.im

instance : Add HurwitzL3 := ⟨fun u v => ⟨hl2Add u.re v.re, hl2Add u.im v.im⟩⟩
instance : Neg HurwitzL3 := ⟨fun u => ⟨hl2Neg u.re, hl2Neg u.im⟩⟩

/-- HurwitzL3 conjugation. -/
def conj (u : HurwitzL3) : HurwitzL3 :=
  ⟨HurwitzL2.conj u.re, hl2Neg u.im⟩

end HurwitzL3

/-! ## §2 — HurwitzL3 units (96 expected) -/

/-- HurwitzL2 zero. -/
def HurwitzL2_zero' : HurwitzL2 := (⟨0, 0⟩ : HurwitzL2)

/-- HurwitzL3 zero. -/
def HurwitzL3_zero : HurwitzL3 := (⟨0, 0⟩ : HurwitzL3)

/-- Lift HurwitzL2 element via re-axis. -/
def HurwitzL3_left (u : HurwitzL2) : HurwitzL3 := ⟨u, HurwitzL2_zero'⟩

/-- Lift HurwitzL2 element via im-axis. -/
def HurwitzL3_right (u : HurwitzL2) : HurwitzL3 := ⟨HurwitzL2_zero', u⟩

/-- HurwitzL3 units = 96 elements: 48 re + 48 im liftings. -/
def HurwitzL3_units : List HurwitzL3 :=
  (HurwitzL2_units.map HurwitzL3_left) ++ (HurwitzL2_units.map HurwitzL3_right)

/-- ★ **HurwitzL3 unit count** = 96 = 2 × 48. -/
theorem HurwitzL3_units_count : HurwitzL3_units.length = 96 := by decide

/-! ## §3 — Capstone -/

/-- ★★★★ **Type D tower L2 capstone**: structural shell witnessing
    that Hurwitz CD-doubling extends past L1.

    Bundles: (a) HurwitzL3 type, (b) operations (mul/conj/normSq/
    hl2Add/hl2Neg/hl2Sub), (c) unit cardinality 96 = 2 × 48,
    (d) doubling relation. -/
theorem hurwitz_tower_L2_capstone :
    HurwitzL3_units.length = 96
    ∧ HurwitzL3_units.length = 2 * HurwitzL2_units.length := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Integer.HurwitzTower
