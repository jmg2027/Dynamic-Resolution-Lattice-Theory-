import E213.Meta.UniversalLens.Core
import E213.Meta.UniversalLens.Nat2
import E213.Meta.UniversalLens.Nat2Inj
import E213.Meta.UniversalLens.Nat3
import E213.Meta.UniversalLens.Nat4
import E213.Meta.UniversalLens.Padding
import E213.Meta.UniversalLens.PaddingCapstone
import E213.Meta.UniversalLens.Q213
import E213.Meta.UniversalLens.Q213Inj
import E213.Meta.UniversalLens.Q213_3
import E213.Meta.UniversalLens.TripleCapstone

/-! Spec-as-code entry point for `E213.Meta.UniversalLens`.

  Universal Lens construction over the Q213 / Nat2 / Nat3 / Nat4
  test codomains.  Concrete witnesses + injectivity + padding +
  triple-capstone integration.

  ## Core

    * `Core`             — the universal-Lens carrier construction

  ## Nat-arity test codomains

    * `Nat2`,
      `Nat2Inj`          — Nat-arity-2 codomain + injectivity
    * `Nat3`              — Nat-arity-3 codomain
    * `Nat4`              — Nat-arity-4 codomain

  ## Q213 (rational) codomain

    * `Q213`             — Q213 universal-Lens witness
    * `Q213Inj`          — Q213 injectivity
    * `Q213_3`           — Q213-arity-3 variant

  ## Padding + capstones

    * `Padding`,
      `PaddingCapstone`  — padding-by-zero witness
    * `TripleCapstone`   — triple integration (Nat × Q × Padding)
-/
