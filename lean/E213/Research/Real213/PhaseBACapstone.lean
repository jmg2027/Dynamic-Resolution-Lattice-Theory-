import E213.Research.Real213.FluxFTC

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

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **Phase BA cohomEquiv bridge arc capstone**: 8-fact bundle. -/
theorem phaseBA_capstone (a b c d : FluxCut) (hab : FluxCut.cohomEquiv a b)
    (hcd : FluxCut.cohomEquiv c d)
    (cf : Nat → Nat → Bool) (db : DyadicBracket) :
    -- (AY-1) cohomEquiv reflexive
    FluxCut.cohomEquiv a a
    -- (AY-1) cohomEquiv symmetric
    ∧ FluxCut.cohomEquiv b a
    -- (AY-2) neg respects cohomEquiv
    ∧ FluxCut.cohomEquiv a.neg b.neg
    -- (AY-2) add respects cohomEquiv pairwise
    ∧ FluxCut.cohomEquiv (FluxCut.add a c) (FluxCut.add b d)
    -- (AY-2) sub respects cohomEquiv pairwise
    ∧ FluxCut.cohomEquiv (FluxCut.sub a c) (FluxCut.sub b d)
    -- (AY-3) MVT for id: localDivergence id unitBracket = ofCut 1
    ∧ FluxCut.localDivergence id unitBracket = FluxCut.ofCut (constCut 1 1)
    -- (AZ) FTC bridge: localDivergence = fluxAlong at unitBracket
    ∧ FluxCut.localDivergence id unitBracket = FluxCut.fluxAlong id unitBracket
    -- (AZ) FTC for constant: divergence balanced
    ∧ FluxCut.isBalanced (FluxCut.localDivergence (constCutFn cf) db) :=
  ⟨FluxCut.cohomEquiv_refl a,
   FluxCut.cohomEquiv_symm a b hab,
   FluxCut.neg_cohomEquiv a b hab,
   FluxCut.add_cohomEquiv a b c d hab hcd,
   FluxCut.sub_cohomEquiv a b c d hab hcd,
   FluxCut.mvt_id_unitBracket,
   FluxCut.ftc_bridge_id_unitBracket,
   FluxCut.localDivergence_const_balanced cf db⟩

end E213.Research.Real213.CutSum
