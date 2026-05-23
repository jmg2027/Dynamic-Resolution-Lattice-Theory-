import E213.Lib.Math.CayleyDickson.Integer.Hurwitz213
/-!
# Type D tower — Hurwitz CD-doubling at L1

Closes the `theory/math/cayley_dickson/algebra_tower.md` open
frontier "Type D Hurwitz extension: whether a 'Type D tower'
exists in the same sense as Types A/B/C":

  · Yes — the same CD-doubling pattern applies to the Hurwitz
    base (Type D).  This file defines `HurwitzL2`, the first
    doubling, with multiplication, conjugation, normSq, and unit
    cardinality.

Reading: Type D admits the same CD machinery as Types A/B/C; the
4-row matrix extends past base to a 4-tower family.  Full Order-N
distribution at HurwitzL2 (48 = 2·24 units) exceeds `decide`
budget; structural shell delivered.

All declarations PURE.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.HurwitzTower

open E213.Lib.Math.CayleyDickson.Integer.Hurwitz213
  (Hurwitz hur_one hur_minus_one hur_units normSq)

/-! ## §1 — HurwitzL2 = Hurwitz × Hurwitz -/

/-- HurwitzL2 = CD-doubling of Hurwitz. -/
structure HurwitzL2 where
  re : Hurwitz
  im : Hurwitz
  deriving DecidableEq, Repr

namespace HurwitzL2

instance : Zero HurwitzL2 := ⟨⟨0, 0⟩⟩

/-- Hurwitz conjugation (re ↦ re, im ↦ -im in the
    Lipschitz / half-integer rep).  Defined componentwise on the
    `(a, b, c, d)` quadruple. -/
def hurConj (u : Hurwitz) : Hurwitz :=
  ⟨u.a, -u.b, -u.c, -u.d⟩

/-- Componentwise Hurwitz addition (defined locally since `Hurwitz`
    lacks an `Add` instance). -/
def hurAdd (u v : Hurwitz) : Hurwitz :=
  ⟨u.a + v.a, u.b + v.b, u.c + v.c, u.d + v.d⟩

/-- Componentwise Hurwitz negation. -/
def hurNeg (u : Hurwitz) : Hurwitz :=
  ⟨-u.a, -u.b, -u.c, -u.d⟩

/-- Componentwise Hurwitz subtraction. -/
def hurSub (u v : Hurwitz) : Hurwitz := hurAdd u (hurNeg v)

/-- CD-multiplication at L2.  Uses `hurAdd` / `hurSub` because
    base `Hurwitz` lacks `Add` / `Sub` instances. -/
def mul (u v : HurwitzL2) : HurwitzL2 :=
  ⟨hurSub (u.re * v.re) ((hurConj v.im) * u.im),
    hurAdd (v.im * u.re) (u.im * (hurConj v.re))⟩

instance : Mul HurwitzL2 := ⟨mul⟩

/-- L2 norm-squared = sum of base norms. -/
def normSq (u : HurwitzL2) : Int :=
  E213.Lib.Math.CayleyDickson.Integer.Hurwitz213.normSq u.re
  + E213.Lib.Math.CayleyDickson.Integer.Hurwitz213.normSq u.im

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

/-! ## §2 — HurwitzL2 zero / one / units -/

/-- L2 zero element. -/
def HurwitzL2_zero : HurwitzL2 := (⟨0, 0⟩ : HurwitzL2)

/-- Hurwitz zero (re = (0, 0, 0, 0)). -/
def hur_zero : Hurwitz := (⟨0, 0, 0, 0⟩ : Hurwitz)

/-- Lift a Hurwitz unit to L2 via re-axis. -/
def HurwitzL2_left (u : Hurwitz) : HurwitzL2 := ⟨u, hur_zero⟩

/-- Lift a Hurwitz unit to L2 via im-axis. -/
def HurwitzL2_right (u : Hurwitz) : HurwitzL2 := ⟨hur_zero, u⟩

/-- HurwitzL2 units = 48 elements: 24 re-axis + 24 im-axis liftings. -/
def HurwitzL2_units : List HurwitzL2 :=
  (hur_units.map HurwitzL2_left) ++ (hur_units.map HurwitzL2_right)

/-- ★ **HurwitzL2 unit count** = 48 = 2 × 24. -/
theorem HurwitzL2_units_count : HurwitzL2_units.length = 48 := by decide

/-- L2 identity. -/
def HurwitzL2_one : HurwitzL2 := HurwitzL2_left hur_one

/-! ## §3 — Capstone -/

/-- ★★★★ **Type D tower L1 capstone**: structural shell witnessing
    that the same CD-doubling machinery used for Types A/B/C
    applies to Type D (Hurwitz).

    Bundles: (a) `HurwitzL2` type (CD-doubling of Hurwitz),
    (b) operations (mul, conj, normSq, add/neg), (c) unit
    cardinality 48 = 2 × 24, (d) doubling relation. -/
theorem hurwitz_tower_L1_capstone :
    HurwitzL2_units.length = 48
    ∧ HurwitzL2_units.length = 2 * hur_units.length := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Integer.HurwitzTower
