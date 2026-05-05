import E213.Meta.Tactic.PureGuard
import E213.Math.PatternCatalogInstance
import E213.Math.PatternCatalogSpan
import E213.Math.PatternCatalogAlgebra

/-!
# PureGuard regression tests for the Pattern Catalog

Asserts at *build time* that representative catalog instances are
∅-pure.  If a future change introduces an axiom leak in any of these,
the build fails — direct kernel-level analogue of `sorry` detection.

This replaces (for these specific declarations) the post-hoc Python
audit `tools/scan_all_axioms.py`: leaks now break the build instead
of being reported afterward.
-/

namespace E213.Meta.Tactic.PureGuardTest

open E213.Meta.Tactic.PureGuard

-- Atomic-game instances
#guard_pure E213.Math.PatternCatalogInstance.cutMulOneOne_localityWitness
#guard_pure E213.Math.PatternCatalogInstance.boolOscillator
#guard_pure E213.Math.PatternCatalogInstance.fiveIsForced

-- Real Lens lifts
#guard_pure E213.Math.PatternCatalogInstance.peanoLensWitness
#guard_pure E213.Math.PatternCatalogInstance.depthLensWitness
#guard_pure E213.Math.PatternCatalogInstance.isLeafLensWitness

-- Composite instances
#guard_pure E213.Math.PatternCatalogInstance.peanoDepthCohabit
#guard_pure E213.Math.PatternCatalogInstance.demoLocalityAggregate
#guard_pure E213.Math.PatternCatalogInstance.pisanoLikeAggregate
#guard_pure E213.Math.PatternCatalogInstance.fanOutCataAggregate
#guard_pure E213.Math.PatternCatalogInstance.boolNatLocalityForced
#guard_pure E213.Math.PatternCatalogInstance.optionCataForcedForm
#guard_pure E213.Math.PatternCatalogInstance.modCounter3WithForcedPeriod

-- Closure instances (DepAggregate + UniformArityNCohabit)
#guard_pure E213.Math.PatternCatalogInstance.heteroDepAggregate
#guard_pure E213.Math.PatternCatalogInstance.threeLensCohabit

-- Free-monoid + anchor + span theorems
#guard_pure E213.Math.PatternCatalogAlgebra.OpWord.append_assoc
#guard_pure E213.Math.PatternCatalogAlgebra.OpWord.aggCount_append
#guard_pure E213.Math.PatternCatalogAlgebra.Locality.anchor
#guard_pure E213.Math.PatternCatalogSpan.finalVerdict

end E213.Meta.Tactic.PureGuardTest
