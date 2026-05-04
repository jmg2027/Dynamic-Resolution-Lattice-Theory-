import E213.Math.PatternCatalog
import E213.Math.Real213.CutMulOne

/-!
# PatternCatalog — instance check

Test whether the four-game catalog of `PatternCatalog.lean` actually
captures real 213 objects.  We try to populate each game with a
concrete instance from the codebase.

## Discovery

`LocalityWitness` requires *both* `f` (global) and `f_at` (pointwise),
plus an `agrees` proof.  But after the session-27 박멸, **the global
form `f` was deleted** for cut algebra.  Only `f_at` remains.

→ The most honest instance is the *trivial self-instance*: take
`f := f_at`.  Then `agrees := fun _ => rfl`.

This is a structural observation: the catalog's "duality" is a
**transitional artifact**, not a permanent feature.  Post-extermination
213 has unified the two sides.  See analysis at end of file.
-/

namespace E213.Math.PatternCatalogInstance

open E213.Math.PatternCatalog
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)

/-- Post-extermination self-instance: `f` and `f_at` are the same
    function (function-eq form was deleted).  Trivially `agrees`. -/
def cutMulOneOne_localityWitness :
    LocalityWitness (Nat × Nat) Bool :=
  { f      := fun ⟨m, k⟩ =>
                cutMul (constCut 1 1) (constCut 1 1) m k
    f_at   := fun ⟨m, k⟩ =>
                cutMul (constCut 1 1) (constCut 1 1) m k
    agrees := fun _ => rfl }

/-- Post-extermination *witness-only* form: drop the redundant `f`. -/
structure LocalityWitnessOnly (Idx : Type) (Val : Type) where
  f_at : Idx → Val

/-- Self-witness at the cut point. -/
def cutMulOneOne_witness :
    LocalityWitnessOnly (Nat × Nat) Bool :=
  { f_at := fun ⟨m, k⟩ =>
              cutMul (constCut 1 1) (constCut 1 1) m k }

end E213.Math.PatternCatalogInstance
