import E213.Math.Real213.FluxFTC

/-!
# Research.Real213PhaseBACapstone

Phase BA: unified capstone for the cohomEquiv bridge arc (AY-AZ).

Bundles every result on the Setoid-level cutEq → propEq bridge:
  AY-1 Setoid (cohomEquiv reflexive/symmetric/transitive)
  AY-2 flux operations preserve cohomEquiv
  AY-3 concrete MVT (id at unitBracket — propEq!)
  AZ   FTC framework + bridge id case (propEq!)

★ Key win: id at unitBracket gives *propositional* equality, not
just cohomEquiv.  The framework provides propEq when reachable,
cohomEquiv when structural reduction blocks it.
-/

namespace E213.Math.Real213.PhaseBACapstone

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCut.FluxCut (ofCut add neg sub)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong isBalanced)
open E213.Math.Real213.FluxDivergence.FluxCut
  (localDivergence localDivergence_const_balanced)
open E213.Math.Real213.FluxMVTConcrete.FluxCut (mvt_id_unitBracket)
open E213.Math.Real213.FluxFTC.FluxCut (ftc_bridge_id_unitBracket)
open E213.Math.Real213.FluxEquiv.FluxCut
  (cohomEquiv cohomEquiv_refl cohomEquiv_symm)
open E213.Math.Real213.FluxEquivOps.FluxCut
  (neg_cohomEquiv add_cohomEquiv sub_cohomEquiv)
open E213.Math.Real213.DyadicTrajectory (unitBracket)

/-- **Phase BA cohomEquiv bridge arc capstone**: 8-fact bundle. -/
theorem phaseBA_capstone (a b c d : FluxCut) (hab : cohomEquiv a b)
    (hcd : cohomEquiv c d)
    (cf : Nat → Nat → Bool) (db : DyadicBracket) :
    -- (AY-1) cohomEquiv reflexive
    cohomEquiv a a
    -- (AY-1) cohomEquiv symmetric
    ∧ cohomEquiv b a
    -- (AY-2) neg respects cohomEquiv
    ∧ cohomEquiv a.neg b.neg
    -- (AY-2) add respects cohomEquiv pairwise
    ∧ cohomEquiv (add a c) (add b d)
    -- (AY-2) sub respects cohomEquiv pairwise
    ∧ cohomEquiv (sub a c) (sub b d)
    -- (AY-3) MVT for id: localDivergence id unitBracket = ofCut 1
    ∧ localDivergence id unitBracket = ofCut (constCut 1 1)
    -- (AZ) FTC bridge: localDivergence = fluxAlong at unitBracket
    ∧ localDivergence id unitBracket = fluxAlong id unitBracket
    -- (AZ) FTC for constant: divergence balanced
    ∧ isBalanced (localDivergence (constCutFn cf) db) :=
  ⟨cohomEquiv_refl a,
   cohomEquiv_symm a b hab,
   neg_cohomEquiv a b hab,
   add_cohomEquiv a b c d hab hcd,
   sub_cohomEquiv a b c d hab hcd,
   mvt_id_unitBracket,
   ftc_bridge_id_unitBracket,
   localDivergence_const_balanced cf db⟩

end E213.Math.Real213.PhaseBACapstone
