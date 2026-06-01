import E213.Meta.Tactic.NativeGuard
import E213.Lib.Math.PatternCatalog.Instance
import E213.Lib.Math.PatternCatalog.Algebra
import E213.Lib.Math.PatternCatalog.Span
import E213.Lib.Math.ResolutionLimit
import E213.Lib.Math.Cohomology.Fractal.ConfigCount

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
#guard_native E213.Lib.Math.PatternCatalog.Instance.cutMulOneOne_localityWitness
#guard_native E213.Lib.Math.PatternCatalog.Instance.boolOscillator
#guard_native E213.Lib.Math.PatternCatalog.Instance.fiveIsForced

-- Real Lens lifts
#guard_native E213.Lib.Math.PatternCatalog.Instance.peanoLensWitness
#guard_native E213.Lib.Math.PatternCatalog.Instance.depthLensWitness
#guard_native E213.Lib.Math.PatternCatalog.Instance.isLeafLensWitness

-- Composite instances
#guard_native E213.Lib.Math.PatternCatalog.Instance.peanoDepthCohabit
#guard_native E213.Lib.Math.PatternCatalog.Instance.demoLocalityAggregate
#guard_native E213.Lib.Math.PatternCatalog.Instance.pisanoLikeAggregate
#guard_native E213.Lib.Math.PatternCatalog.Instance.fanOutCataAggregate

-- Closure instances
#guard_native E213.Lib.Math.PatternCatalog.Instance.heteroDepAggregate
#guard_native E213.Lib.Math.PatternCatalog.Instance.threeLensCohabit

-- Free-monoid theorems
#guard_native E213.Lib.Math.PatternCatalog.Algebra.OpWord.append_assoc
#guard_native E213.Lib.Math.PatternCatalog.Algebra.OpWord.append_nil
#guard_native E213.Lib.Math.PatternCatalog.Algebra.OpWord.aggCount_append

-- Anchor records (213-원론 anchors)
#guard_native E213.Lib.Math.PatternCatalog.Algebra.Locality.anchor
#guard_native E213.Lib.Math.PatternCatalog.Algebra.AggregateOp.anchor
#guard_native E213.Lib.Math.PatternCatalog.Algebra.ForcedOp.anchor

-- Span verdict
#guard_native E213.Lib.Math.PatternCatalog.Span.finalVerdict

-- Cantor anchor + parametric configuration count
#guard_native E213.Lib.Math.ResolutionLimit.cantor_inhabitant_absence
#guard_native E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCountD

end E213.Meta.Tactic.NativeGuardTest
