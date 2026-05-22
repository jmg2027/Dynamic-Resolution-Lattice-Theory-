import E213.Lib.Math.Cohomology.Fractal.AlphaGUT
import E213.Lib.Math.Cohomology.Fractal.ConfigCount
import E213.Lib.Math.Cohomology.Fractal.Level
import E213.Lib.Math.Cohomology.Fractal.V25

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Fractal`.

  Fractal-lens cardinality scaffold.  Per G120 Round 3 (2026-05-22):
  the parametric family `configCount : Nat → Nat` is the canonical
  Lens-output object; the historical `N_U = 5²⁵` is one value
  (`configCount 2`), not a privileged constant.

  ## Files

    * `Level`        — fractal level definition + parametric
                       `numV (L : Nat) := 5^L`
    * `ConfigCount`  — parametric configuration-count family
                       `configCount (n : Nat) := 5^(numV n)`
                       (G120 Phase 1)
    * `V25`          — 5²⁵ enumeration witness at level 2
    * `AlphaGUT`     — α_GUT = 6/(25π²) as the level-2 fractal
                       cardinality ratio
-/
