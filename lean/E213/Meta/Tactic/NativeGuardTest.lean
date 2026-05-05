import E213.Meta.Tactic.NativeGuard
import E213.Math.PatternCatalogInstance
import E213.Math.PatternCatalogAlgebra
import E213.Math.PatternCatalogSpan
import E213.Math.ResolutionLimit

/-!
# NativeGuard regression tests for the Pattern Catalog

Asserts at *build time* that representative catalog declarations
reference only 213-native vocabulary (E213.* + small Lean Init
allow-list).  Together with `PureGuardTest.lean` this gives the
catalog two complementary build-time guarantees:

  · PureGuard   : zero kernel-axiom dependencies
  · NativeGuard : zero non-E213 vocabulary dependencies

A declaration passing both is **213-pure** in the strongest sense.
-/

namespace E213.Meta.Tactic.NativeGuardTest

open E213.Meta.Tactic.NativeGuard

-- Atomic-game instances
#guard_native E213.Math.PatternCatalogInstance.cutMulOneOne_localityWitness
#guard_native E213.Math.PatternCatalogInstance.boolOscillator
#guard_native E213.Math.PatternCatalogInstance.fiveIsForced

-- Real Lens lifts
#guard_native E213.Math.PatternCatalogInstance.peanoLensWitness
#guard_native E213.Math.PatternCatalogInstance.depthLensWitness
#guard_native E213.Math.PatternCatalogInstance.isLeafLensWitness

-- Composite instances
#guard_native E213.Math.PatternCatalogInstance.peanoDepthCohabit
#guard_native E213.Math.PatternCatalogInstance.demoLocalityAggregate
#guard_native E213.Math.PatternCatalogInstance.pisanoLikeAggregate
#guard_native E213.Math.PatternCatalogInstance.fanOutCataAggregate

-- Closure instances
#guard_native E213.Math.PatternCatalogInstance.heteroDepAggregate
#guard_native E213.Math.PatternCatalogInstance.threeLensCohabit

-- Free-monoid theorems
#guard_native E213.Math.PatternCatalogAlgebra.OpWord.append_assoc
#guard_native E213.Math.PatternCatalogAlgebra.OpWord.append_nil
#guard_native E213.Math.PatternCatalogAlgebra.OpWord.aggCount_append

-- Anchor records (213-원론 anchors)
#guard_native E213.Math.PatternCatalogAlgebra.Locality.anchor
#guard_native E213.Math.PatternCatalogAlgebra.AggregateOp.anchor
#guard_native E213.Math.PatternCatalogAlgebra.ForcedOp.anchor

-- Span verdict
#guard_native E213.Math.PatternCatalogSpan.finalVerdict

-- ResolutionLimit (canonical infinity/N_U spec)
#guard_native E213.Math.ResolutionLimit.N_U
#guard_native E213.Math.ResolutionLimit.cantor_inhabitant_absence
#guard_native E213.Math.ResolutionLimit.resolutionInvariantWitness

end E213.Meta.Tactic.NativeGuardTest
