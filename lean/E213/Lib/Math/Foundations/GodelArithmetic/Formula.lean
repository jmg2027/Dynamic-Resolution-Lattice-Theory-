/-!
# Formula syntax — a tiny formal language (∅-axiom)

A minimal inductive formula type to demonstrate concrete syntax.

## Phase 1 scope

  * Inductive `Formula` with `atom`, `not`, `and`, `imp`.
  * Structural depth + leaf count (∅-axiom).
  * Gödel numbering shape (injectivity left to Phase 2).

The diagonal lemma for real Gödel needs additionally:
  * substitution operation,
  * injective Gödel-numbering,
  * the substitution-via-self-numbering fixed-point construction.
-/

namespace E213.Lib.Math.Foundations.GodelArithmetic.Formula

/-- A minimal formal-language formula. -/
inductive Formula : Type
  | atom : Nat → Formula
  | not  : Formula → Formula
  | and  : Formula → Formula → Formula
  | imp  : Formula → Formula → Formula
  deriving DecidableEq

/-- Structural depth. -/
def Formula.depth : Formula → Nat
  | .atom _ => 0
  | .not f => f.depth + 1
  | .and f g => max f.depth g.depth + 1
  | .imp f g => max f.depth g.depth + 1

theorem depth_atom (n : Nat) : (Formula.atom n).depth = 0 := rfl
theorem depth_not (f : Formula) :
    (Formula.not f).depth = f.depth + 1 := rfl

/-- Leaf count (number of atoms in the formula). -/
def Formula.leafCount : Formula → Nat
  | .atom _ => 1
  | .not f => f.leafCount
  | .and f g => f.leafCount + g.leafCount
  | .imp f g => f.leafCount + g.leafCount

theorem leafCount_atom (n : Nat) :
    (Formula.atom n).leafCount = 1 := rfl

/-- A 4-way tagged Gödel-numbering shape (Phase 1, no injectivity). -/
def Formula.encode : Formula → Nat
  | .atom n => 4 * n
  | .not f => 4 * f.encode + 1
  | .and f g => 4 * (f.encode + g.encode * 1000) + 2
  | .imp f g => 4 * (f.encode + g.encode * 1000) + 3

theorem encode_atom (n : Nat) :
    (Formula.atom n).encode = 4 * n := rfl

theorem encode_not (f : Formula) :
    (Formula.not f).encode = 4 * f.encode + 1 := rfl

theorem encode_and (f g : Formula) :
    (Formula.and f g).encode = 4 * (f.encode + g.encode * 1000) + 2 := rfl

theorem encode_imp (f g : Formula) :
    (Formula.imp f g).encode = 4 * (f.encode + g.encode * 1000) + 3 := rfl

end E213.Lib.Math.Foundations.GodelArithmetic.Formula
