import E213.Math.Cohomology.Dyadic.Pell.Bounds
import E213.Math.Cohomology.Dyadic.Pell.Capstone
import E213.Math.Cohomology.Dyadic.Pell.Family
import E213.Math.Cohomology.Dyadic.Pell.Lens
import E213.Math.Cohomology.Dyadic.Pell.LensPairs
import E213.Math.Cohomology.Dyadic.Pell.LensTriple
import E213.Math.Cohomology.Dyadic.Pell.Proper
import E213.Math.Cohomology.Dyadic.Pell.Proper8
import E213.Math.Cohomology.Dyadic.Pell.ProperMod11
import E213.Math.Cohomology.Dyadic.Pell.ProperMod13
import E213.Math.Cohomology.Dyadic.Pell.ProperMod17
import E213.Math.Cohomology.Dyadic.Pell.ProperMod19
import E213.Math.Cohomology.Dyadic.Pell.ProperMod23
import E213.Math.Cohomology.Dyadic.Pell.ProperSmall

/-! Spec-as-code entry point for `E213.Math.Cohomology.Dyadic.Pell`.

  Pell-equation cluster — `x² - D y² = 1` and its dyadic-FSM
  encoding.

  ## Core

    * `Family`,
      `Bounds`        — Pell solution family + bound lemmas
    * `Capstone`      — top-level Pell capstone

  ## Lens encodings

    * `Lens`          — single-Lens encoding
    * `LensPairs`     — Lens-pair classifier
    * `LensTriple`    — Lens-triple classifier

  ## Proper-Pell (norm-form variant)

    * `Proper`        — proper-Pell core
    * `ProperSmall`   — small-D variant
    * `Proper8`,
      `ProperMod11`,
      `ProperMod13`,
      `ProperMod17`,
      `ProperMod19`,
      `ProperMod23`   — per-mod proper-Pell variants

  ## Status

  14/15 included.  One deferred: `ProperBridge`
  (pre-existing function-application type-mismatch).
-/
