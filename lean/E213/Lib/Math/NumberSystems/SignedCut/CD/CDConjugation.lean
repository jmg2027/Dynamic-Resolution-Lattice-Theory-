import E213.Lib.Math.NumberSystems.SignedCut.CD.CDTowerLevel
import E213.Lib.Math.NumberSystems.SignedCut.Core.Core

/-!
# CD Tower — recursive conjugation involution (∅-axiom)

Cayley-Dickson conjugation is self-similar across levels:
`(a, b)̄ = (ā, neg b)`.  At level 0 it's identity; at every
higher level the recursion flips the imaginary half.

This is the **operationally minimal preserved structure** of
the entire CD tower — survives loss of ordering, commutativity,
associativity, alternativity, ..., at every level `n`.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.CD.CDConjugation

open E213.Lib.Math.NumberSystems.SignedCut.CD.CDTowerLevel (CDLevel)

/-- Recursive conjugation on `CDLevel n`. -/
def cdConj : (n : Nat) → CDLevel n → CDLevel n
  | 0,     z => z
  | _ + 1, z => (cdConj _ z.1, z.2)

/-- ★ Level-0 conjugation = identity (rfl). -/
theorem cdConj_zero (z : CDLevel 0) : cdConj 0 z = z := rfl

/-- ★ Level-1 conjugation acts on first component. -/
theorem cdConj_one (z : CDLevel 1) :
    cdConj 1 z = (z.1, z.2) := rfl

/-- ★ Level-2 conjugation recurses on first component. -/
theorem cdConj_two (z : CDLevel 2) :
    cdConj 2 z = (cdConj 1 z.1, z.2) := rfl

/-- ★ **Involutivity at level 0** (rfl). -/
theorem cdConj_involutive_zero (z : CDLevel 0) :
    cdConj 0 (cdConj 0 z) = z := rfl

/-- ★ **First component preserved by conj-conj**. -/
theorem cdConj_involutive_fst (n : Nat) (z : CDLevel (n + 1)) :
    cdConj n (cdConj n z.1) = z.1 :=
  cdConj_involutive_aux n z.1
where cdConj_involutive_aux : ∀ (n : Nat) (z : CDLevel n),
    cdConj n (cdConj n z) = z
  | 0, _ => rfl
  | _ + 1, z => Prod.ext (cdConj_involutive_aux _ z.1) rfl

/-- ★ **General involutivity** by induction on level. -/
theorem cdConj_involutive : ∀ (n : Nat) (z : CDLevel n),
    cdConj n (cdConj n z) = z
  | 0, _ => rfl
  | _ + 1, z => Prod.ext (cdConj_involutive _ z.1) rfl

end E213.Lib.Math.NumberSystems.SignedCut.CD.CDConjugation
