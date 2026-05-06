import E213.Meta.Tactic.PureGuard
import E213.Math.PatternCatalog.Instance
import E213.Math.PatternCatalog.Span
import E213.Math.PatternCatalog.Algebra
import E213.Math.ResolutionLimit

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
#guard_pure E213.Math.PatternCatalog.Instance.cutMulOneOne_localityWitness
#guard_pure E213.Math.PatternCatalog.Instance.boolOscillator
#guard_pure E213.Math.PatternCatalog.Instance.fiveIsForced

-- Real Lens lifts
#guard_pure E213.Math.PatternCatalog.Instance.peanoLensWitness
#guard_pure E213.Math.PatternCatalog.Instance.depthLensWitness
#guard_pure E213.Math.PatternCatalog.Instance.isLeafLensWitness

-- Composite instances
#guard_pure E213.Math.PatternCatalog.Instance.peanoDepthCohabit
#guard_pure E213.Math.PatternCatalog.Instance.demoLocalityAggregate
#guard_pure E213.Math.PatternCatalog.Instance.pisanoLikeAggregate
#guard_pure E213.Math.PatternCatalog.Instance.fanOutCataAggregate
#guard_pure E213.Math.PatternCatalog.Instance.boolNatLocalityForced
#guard_pure E213.Math.PatternCatalog.Instance.optionCataForcedForm
#guard_pure E213.Math.PatternCatalog.Instance.modCounter3WithForcedPeriod

-- Closure instances (DepAggregate + UniformArityNCohabit)
#guard_pure E213.Math.PatternCatalog.Instance.heteroDepAggregate
#guard_pure E213.Math.PatternCatalog.Instance.threeLensCohabit

-- Free-monoid + anchor + span theorems
#guard_pure E213.Math.PatternCatalog.Algebra.OpWord.append_assoc
#guard_pure E213.Math.PatternCatalog.Algebra.OpWord.aggCount_append
#guard_pure E213.Math.PatternCatalog.Algebra.Locality.anchor
#guard_pure E213.Math.PatternCatalog.Span.finalVerdict

-- ResolutionLimit (canonical infinity/N_U spec, formalised)
#guard_pure E213.Math.ResolutionLimit.N_U
#guard_pure E213.Math.ResolutionLimit.N_U_value
#guard_pure E213.Math.ResolutionLimit.N_U_tensor
#guard_pure E213.Math.ResolutionLimit.cantor_inhabitant_absence
#guard_pure E213.Math.ResolutionLimit.resolutionInvariantWitness

end E213.Meta.Tactic.PureGuardTest
