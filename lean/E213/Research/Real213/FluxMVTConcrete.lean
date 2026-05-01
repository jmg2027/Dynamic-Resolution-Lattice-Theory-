import E213.Research.Real213.FluxEquivOps
import E213.Research.Real213.CutMulOne

/-!
# Research.Real213FluxMVTConcrete

Phase AY-3: **Concrete MVT** via cohomEquiv.

For specific functions and brackets, the localDivergence cohomEquiv
matches the (scaled) flux of the derivative.  Avoids the "general
MVT" wall by leveraging cutMul_one_one / cutMul_one_const for the
unit bracket case.

  mvt_id_unitBracket    : id at unitBracket — full propEq
  mvt_const_unitBracket : constant function at unitBracket
  mvt_const_balanced    : constant function divergence is balanced (any bracket)
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

namespace FluxCut

/-- **MVT for identity at unitBracket**: localDivergence id unitBracket
    propositionally equals ofCut (constCut 1 1).  Since id.derivative
    is constant 1, MVT holds with c being any point. -/
theorem mvt_id_unitBracket :
    localDivergence id unitBracket = ofCut (constCut 1 1) := by
  show ({ forward := cutScale (2^0) 1 (constCut 1 1),
          backward := cutScale (2^0) 1 (constCut 0 1) } : FluxCut)
       = ofCut (constCut 1 1)
  show ({ forward := cutMul (constCut 1 1) (constCut 1 1),
          backward := cutMul (constCut 1 1) (constCut 0 1) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_one_const 0 1]

/-- **MVT corollary**: id's localDivergence at unitBracket is
    cohomEquiv to derivative flux. -/
theorem mvt_id_unitBracket_cohomEquiv :
    cohomEquiv (localDivergence id unitBracket)
               (ofCut (idIsDifferentiable.derivative (constCut 0 1))) := by
  show cohomEquiv (localDivergence id unitBracket)
                  (ofCut ((idIsDifferentiable.derivative) (constCut 0 1)))
  rw [mvt_id_unitBracket]
  show cohomEquiv (ofCut (constCut 1 1)) (ofCut (constCut 1 1))
  exact cohomEquiv_refl _

/-- **MVT for constant at any bracket**: divergence is balanced. -/
theorem mvt_const_balanced (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (localDivergence (constCutFn c) db) :=
  localDivergence_const_balanced c db

/-- **Constant function MVT statement**: divergence cohomEquiv to
    a self-equal flux (any cut, since balanced means forward = backward). -/
theorem mvt_const_self_cohomEquiv (c : Nat → Nat → Bool) (db : DyadicBracket) :
    cohomEquiv (localDivergence (constCutFn c) db)
               { forward := (localDivergence (constCutFn c) db).backward,
                 backward := (localDivergence (constCutFn c) db).backward } := by
  refine ⟨?_, ?_⟩
  · intro m k
    exact (mvt_const_balanced c db m k)
  · intro m k
    rfl

end FluxCut

end E213.Research.Real213.CutSum
