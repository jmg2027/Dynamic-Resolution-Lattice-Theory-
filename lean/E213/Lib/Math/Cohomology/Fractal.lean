import E213.Lib.Math.Cohomology.Fractal.AlphaGUT
import E213.Lib.Math.Cohomology.Fractal.ConfigCount
import E213.Lib.Math.Cohomology.Fractal.ConfigCountModular
import E213.Lib.Math.Cohomology.Fractal.Level
import E213.Lib.Math.Cohomology.Fractal.V25
import E213.Lib.Math.Cohomology.Fractal.AltPrimitiveSet
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2PowCutoff
import E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuilleanParam
import E213.Lib.Math.Cohomology.Fractal.EventualPeriodicity
import E213.Lib.Math.Cohomology.Fractal.HunterAtomicClosure
import E213.Lib.Math.Cohomology.Fractal.PisanoGridCapstone

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Fractal`.

  Fractal-lens cardinality scaffold.  The canonical object is the
  2-parameter count-Lens family
    `configCountD (d n : Nat) : Nat := d ^ (d ^ n)`
  parametric in both base `d` and level `n`.  The `d = 5`
  specialisation `configCount n := configCountD 5 n` is the slice
  selected at the physics lens by
  `Theory.Atomicity.Five.atomic_iff_five`; the level-2 value
  `configCount 2 = 5^25` is one value of the family, not a
  privileged constant.

  ## Files

    * `Level`        — fractal level definition + base-5 vertex
                       count `numV (L : Nat) := 5^L`
    * `ConfigCount`  — parametric configuration-count family
                       `configCountD (d n : Nat) := d^(d^n)`,
                       with `configCount` the `d = 5` alias
                       (clean recursion, monotonicity, per-d table)
    * `ConfigCountModular` — `configCountD d n % p` per-prime
                       decide-checked table (d = 5, small p)
                       + cross-base level-2 sample at p = 7
    * `V25`          — `5²⁵` enumeration witness at level 2
    * `AlphaGUT`     — `α_GUT = 6/(25π²)` as the level-2 fractal
                       cardinality ratio
-/
