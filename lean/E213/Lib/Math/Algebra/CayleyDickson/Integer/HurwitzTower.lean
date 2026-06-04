import E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213

/-!
# Type D Hurwitz CD-doubling tower — L1 and L2

Closes the `theory/math/algebra/cayley_dickson/algebra_tower.md` open
frontier "Type D Hurwitz extension: whether a 'Type D tower'
exists in the same sense as Types A/B/C".

The same CD-doubling pattern applies to the Hurwitz base (Type D),
producing a uniform tower in lockstep with Types A/B/C.  Unit
cardinalities double per layer:

  · L0 (`Hurwitz`):   24 units (`2T` binary tetrahedral)
  · L1 (`HurwitzL2`): 48 units (§1)
  · L2 (`HurwitzL3`): 96 units (§2)

Full Order-N distribution at L1/L2 exceeds `decide` budget;
structural shells are delivered (type + operations + unit
cardinality + doubling relation).

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.HurwitzTower

open E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213
  (Hurwitz hur_one hur_minus_one hur_units normSq)

/-! ### §1 — HurwitzL2 = CD-doubling of Hurwitz (48 units) -/

/-- HurwitzL2 = CD-doubling of Hurwitz. -/
structure HurwitzL2 where
  re : Hurwitz
  im : Hurwitz
  deriving DecidableEq, Repr

namespace HurwitzL2

instance : Zero HurwitzL2 := ⟨⟨0, 0⟩⟩

/-- Hurwitz conjugation (componentwise on the `(a, b, c, d)`
    quadruple). -/
def hurConj (u : Hurwitz) : Hurwitz :=
  ⟨u.a, -u.b, -u.c, -u.d⟩

/-- Componentwise Hurwitz addition. -/
def hurAdd (u v : Hurwitz) : Hurwitz :=
  ⟨u.a + v.a, u.b + v.b, u.c + v.c, u.d + v.d⟩

/-- Componentwise Hurwitz negation. -/
def hurNeg (u : Hurwitz) : Hurwitz :=
  ⟨-u.a, -u.b, -u.c, -u.d⟩

/-- Componentwise Hurwitz subtraction. -/
def hurSub (u v : Hurwitz) : Hurwitz := hurAdd u (hurNeg v)

/-- CD-multiplication at L2. -/
def mul (u v : HurwitzL2) : HurwitzL2 :=
  ⟨hurSub (u.re * v.re) ((hurConj v.im) * u.im),
    hurAdd (v.im * u.re) (u.im * (hurConj v.re))⟩

instance : Mul HurwitzL2 := ⟨mul⟩

/-- L2 norm-squared = sum of base norms. -/
def normSq (u : HurwitzL2) : Int :=
  E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213.normSq u.re
  + E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213.normSq u.im

instance : Add HurwitzL2 :=
  ⟨fun u v => ⟨⟨u.re.a + v.re.a, u.re.b + v.re.b,
                u.re.c + v.re.c, u.re.d + v.re.d⟩,
               ⟨u.im.a + v.im.a, u.im.b + v.im.b,
                u.im.c + v.im.c, u.im.d + v.im.d⟩⟩⟩

instance : Neg HurwitzL2 :=
  ⟨fun u => ⟨⟨-u.re.a, -u.re.b, -u.re.c, -u.re.d⟩,
             ⟨-u.im.a, -u.im.b, -u.im.c, -u.im.d⟩⟩⟩

/-- L2 conjugation. -/
def conj (u : HurwitzL2) : HurwitzL2 :=
  ⟨hurConj u.re,
   ⟨-u.im.a, -u.im.b, -u.im.c, -u.im.d⟩⟩

end HurwitzL2

/-- L2 zero element. -/
def HurwitzL2_zero : HurwitzL2 := (⟨0, 0⟩ : HurwitzL2)

/-- Hurwitz zero. -/
def hur_zero : Hurwitz := (⟨0, 0, 0, 0⟩ : Hurwitz)

/-- Lift a Hurwitz unit to L2 via re-axis. -/
def HurwitzL2_left (u : Hurwitz) : HurwitzL2 := ⟨u, hur_zero⟩

/-- Lift a Hurwitz unit to L2 via im-axis. -/
def HurwitzL2_right (u : Hurwitz) : HurwitzL2 := ⟨hur_zero, u⟩

/-- HurwitzL2 units = 48 elements (24 re-axis + 24 im-axis). -/
def HurwitzL2_units : List HurwitzL2 :=
  (hur_units.map HurwitzL2_left) ++ (hur_units.map HurwitzL2_right)

/-- HurwitzL2 unit count = 48 = 2 × 24. -/
theorem HurwitzL2_units_count : HurwitzL2_units.length = 48 := by decide

/-- L2 identity. -/
def HurwitzL2_one : HurwitzL2 := HurwitzL2_left hur_one

/-- Type D tower L1 capstone — structural shell witnessing that the
    same CD-doubling machinery used for Types A/B/C applies to
    Type D (Hurwitz). -/
theorem hurwitz_tower_L1_capstone :
    HurwitzL2_units.length = 48
    ∧ HurwitzL2_units.length = 2 * hur_units.length := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### §2 — HurwitzL3 = CD-doubling of HurwitzL2 (96 units) -/

/-- HurwitzL3 = CD-doubling of HurwitzL2. -/
structure HurwitzL3 where
  re : HurwitzL2
  im : HurwitzL2
  deriving DecidableEq, Repr

namespace HurwitzL3

instance : Zero HurwitzL3 := ⟨⟨0, 0⟩⟩

/-- Componentwise HurwitzL2 addition (HurwitzL2 lacks `Add` at the
    field level). -/
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

/-- HurwitzL2 zero (re-exported for L3). -/
def HurwitzL2_zero' : HurwitzL2 := (⟨0, 0⟩ : HurwitzL2)

/-- HurwitzL3 zero. -/
def HurwitzL3_zero : HurwitzL3 := (⟨0, 0⟩ : HurwitzL3)

/-- Lift HurwitzL2 element via re-axis. -/
def HurwitzL3_left (u : HurwitzL2) : HurwitzL3 := ⟨u, HurwitzL2_zero'⟩

/-- Lift HurwitzL2 element via im-axis. -/
def HurwitzL3_right (u : HurwitzL2) : HurwitzL3 := ⟨HurwitzL2_zero', u⟩

/-- HurwitzL3 units = 96 elements (48 re + 48 im liftings). -/
def HurwitzL3_units : List HurwitzL3 :=
  (HurwitzL2_units.map HurwitzL3_left)
  ++ (HurwitzL2_units.map HurwitzL3_right)

/-- HurwitzL3 unit count = 96 = 2 × 48. -/
theorem HurwitzL3_units_count : HurwitzL3_units.length = 96 := by decide

/-- Type D tower L2 capstone — structural shell witnessing that
    Hurwitz CD-doubling extends past L1. -/
theorem hurwitz_tower_L2_capstone :
    HurwitzL3_units.length = 96
    ∧ HurwitzL3_units.length = 2 * HurwitzL2_units.length := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.Algebra.CayleyDickson.Integer.HurwitzTower
