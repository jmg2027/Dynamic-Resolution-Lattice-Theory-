import E213.Lib.Math.DyadicFSM.Pell.Bounds
import E213.Lib.Math.DyadicFSM.Pell.Capstone
import E213.Lib.Math.DyadicFSM.Pell.Family
import E213.Lib.Math.DyadicFSM.Pell.Lens
import E213.Lib.Math.DyadicFSM.Pell.LensPairs
import E213.Lib.Math.DyadicFSM.Pell.LensTriple
import E213.Lib.Math.DyadicFSM.Pell.Proper
import E213.Lib.Math.DyadicFSM.Pell.Proper8
import E213.Lib.Math.DyadicFSM.Pell.ProperBridge
import E213.Lib.Math.DyadicFSM.Pell.ProperMod
import E213.Lib.Math.DyadicFSM.Pell.ProperSmall

/-! Spec-as-code entry point for `E213.Lib.Math.DyadicFSM.Pell`.

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
    * `Proper8`       — proper-Pell mod 8 specialisation
    * `ProperMod`     — per-prime instances `p ∈ {11, 13, 17, 19, 23}`
                        bundled as sub-namespaces `Pell.ProperMod{p}`
    * `ProperBridge`  — bridge to ArithFSM
-/
