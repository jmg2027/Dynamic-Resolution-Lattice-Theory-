import E213.Lib.Math.Probability.Foundation.Cut
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket

/-!
# Probability — `UniformOnUnit`

The uniform distribution on the unit interval, atomic form.

A `DyadicBracket [a/2^E, b/2^E]` contained in `[0, 1]` carries
uniform probability mass `(b − a) / 2^E = lenNum / 2^expE`.

This is the `(b − a)/2^E` propEq promised in the blueprint:
length-of-bracket / total-length, with no integration step needed —
just structural data.
-/

namespace E213.Lib.Math.Probability.Distribution.UniformOnUnit

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Probability.Foundation.Cut (ProbabilityCut)

/-- A *unit sub-bracket*: a `DyadicBracket` contained in `[0, 1]`,
    enforced by `numB ≤ 2^expE`. -/
structure UnitSubBracket where
  db : DyadicBracket
  contained : db.numB ≤ 2 ^ db.expE

namespace UnitSubBracket

/-- The whole unit `[0, 1]` is itself a unit sub-bracket. -/
def whole : UnitSubBracket where
  db :=
    { numA := 0
      numB := 1
      expE := 0
      hLe := Nat.zero_le 1 }
  contained := Nat.le_refl 1

/-- The uniform probability mass of a unit sub-bracket: `lenNum / 2^expE`.
    *Mass = length of bracket* (denominator is the unit's atomic
    resolution). -/
def uniform (u : UnitSubBracket) : ProbabilityCut where
  num := u.db.lenNum
  den := 2 ^ u.db.expE
  den_pos := Nat.pos_pow_of_pos u.db.expE (Nat.zero_lt_succ 1)
  mass_le :=
    -- lenNum = numB − numA ≤ numB ≤ 2^expE
    Nat.le_trans (Nat.sub_le u.db.numB u.db.numA) u.contained

/-- Mass of the whole `[0, 1]` is `1/1 = 1` (rfl). -/
theorem uniform_whole_num : (uniform whole).num = 1 := rfl

/-- Denominator of `uniform whole` is `2^0 = 1` (rfl). -/
theorem uniform_whole_den : (uniform whole).den = 1 := rfl

/-- **Uniform mass propEq**: for any unit sub-bracket,
    `(uniform u).num = u.db.numB − u.db.numA` and `den = 2 ^ u.db.expE`.
    This is the `(b − a)/2^E` form from the blueprint. -/
theorem uniform_mass_eq (u : UnitSubBracket) :
    (uniform u).num = u.db.numB - u.db.numA
    ∧ (uniform u).den = 2 ^ u.db.expE :=
  ⟨rfl, rfl⟩

end UnitSubBracket

end E213.Lib.Math.Probability.Distribution.UniformOnUnit
