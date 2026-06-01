import E213.Meta.Tactic.PureGuard
import E213.Lib.Math.PatternCatalog.Instance
import E213.Lib.Math.PatternCatalog.Span
import E213.Lib.Math.PatternCatalog.Algebra
import E213.Lib.Math.ResolutionLimit
import E213.Lib.Math.Cohomology.Fractal.ConfigCount

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
#guard_pure E213.Lib.Math.PatternCatalog.Instance.cutMulOneOne_localityWitness
#guard_pure E213.Lib.Math.PatternCatalog.Instance.boolOscillator
#guard_pure E213.Lib.Math.PatternCatalog.Instance.fiveIsForced

-- Real Lens lifts
#guard_pure E213.Lib.Math.PatternCatalog.Instance.peanoLensWitness
#guard_pure E213.Lib.Math.PatternCatalog.Instance.depthLensWitness
#guard_pure E213.Lib.Math.PatternCatalog.Instance.isLeafLensWitness

-- Composite instances
#guard_pure E213.Lib.Math.PatternCatalog.Instance.peanoDepthCohabit
#guard_pure E213.Lib.Math.PatternCatalog.Instance.demoLocalityAggregate
#guard_pure E213.Lib.Math.PatternCatalog.Instance.pisanoLikeAggregate
#guard_pure E213.Lib.Math.PatternCatalog.Instance.fanOutCataAggregate
#guard_pure E213.Lib.Math.PatternCatalog.Instance.boolNatLocalityForced
#guard_pure E213.Lib.Math.PatternCatalog.Instance.optionCataForcedForm
#guard_pure E213.Lib.Math.PatternCatalog.Instance.modCounter3WithForcedPeriod

-- Closure instances (DepAggregate + UniformArityNCohabit)
#guard_pure E213.Lib.Math.PatternCatalog.Instance.heteroDepAggregate
#guard_pure E213.Lib.Math.PatternCatalog.Instance.threeLensCohabit

-- Free-monoid + anchor + span theorems
#guard_pure E213.Lib.Math.PatternCatalog.Algebra.OpWord.append_assoc
#guard_pure E213.Lib.Math.PatternCatalog.Algebra.OpWord.aggCount_append
#guard_pure E213.Lib.Math.PatternCatalog.Algebra.Locality.anchor
#guard_pure E213.Lib.Math.PatternCatalog.Span.finalVerdict

-- Cantor / Cauchy ∅-axiom type-distinction anchors + parametric count
#guard_pure E213.Lib.Math.ResolutionLimit.cantor_inhabitant_absence
#guard_pure E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCountD
#guard_pure E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCountD_succ
#guard_pure E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCount_two

end E213.Meta.Tactic.PureGuardTest
