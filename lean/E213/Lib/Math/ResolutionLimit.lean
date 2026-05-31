import E213.Lens.Cardinality
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory

/-!
# ∅-axiom infinity type-distinction anchors (Cantor + Cauchy)

Two ∅-axiom-witnessed type distinctions that block ZFC-style
infinity collapse, exposed here as spec-level entry points:

  · Cantor "inhabitant absence" — no constructive surjection onto a
    power type.
  · Cauchy "structural inequality" — a dyadic trajectory and its
    supposed exact value live at distinct types.

The parametric configuration count `configCountD d n = d^(d^n)` lives
in `Lib/Math/Cohomology/Fractal/ConfigCount.lean`; arithmetic facts
about its level-2 value are `configCount_two` / `configCount_two_pow`
there.  No privileged level is selected here.

∅-axiom + 213-native verified (PureGuardTest / NativeGuardTest).
-/

namespace E213.Lib.Math.ResolutionLimit

/-! ## §1 — Cantor: inhabitant absence

Cantor's theorem holds in 213 by **inhabitant absence**: under
intuitionistic logic in the ∅-axiom regime, no constructive
trajectory can be assembled to satisfy `Surjective f` for any
`f : X → (X → Bool)`. -/

/-- Canonical Cantor reference: `cantor_general` from
    `Lens/Cardinality`. -/
theorem cantor_inhabitant_absence (X : Type) :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f :=
  E213.Lens.Cardinality.cantor_general

/-! ## §2 — Cauchy: structural inequality preservation

The trajectory object and its supposed exact value live at
distinct types in ∅-axiom regime.  ZFC merges them via
`propext` / `Quot.sound` quotient on the Cauchy equivalence;
∅-axiom does not admit either, so the type distinction stands. -/

/-- Canonical Cauchy reference: trajectory and exact value are
    structurally distinct.  Same type as
    `alwaysTrueUnit_limit_distinct_from_zero` from the
    DyadicTrajectory module — exposed here as the spec-level entry. -/
abbrev cauchy_structural_inequality :=
  @E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero

end E213.Lib.Math.ResolutionLimit
