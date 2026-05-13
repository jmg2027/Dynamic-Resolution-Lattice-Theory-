import E213.Lens.Universal.Flat
import E213.Lens.Universal.QuotLens
import E213.Lens.Universal.Witnesses.Core
import E213.Lens.Universal.Witnesses.Nat2
import E213.Lens.Universal.Witnesses.Nat2Inj
import E213.Lens.Universal.Witnesses.Nat3
import E213.Lens.Universal.Witnesses.Nat4
import E213.Lens.Universal.Witnesses.Padding
import E213.Lens.Universal.Witnesses.PaddingCapstone
import E213.Lens.Universal.Witnesses.Q213
import E213.Lens.Universal.Witnesses.Q213Inj
import E213.Lens.Universal.Witnesses.Q213_3
import E213.Lens.Universal.Witnesses.TripleCapstone

/-! Spec-as-code entry point for `E213.Lens.Universal`.

  Universal Lens construction + concrete witnesses.

  ## Construction (Tier 1)

    * `Flat`     — flat-Lens construction (no internal structure)
    * `QuotLens` — quotient-Lens for a slash-congruence;
                   inverse to `Lens.equiv`

  ## Witnesses (sub-cluster — concrete instances)

    * `Witnesses/Core`             — universal-Lens carrier
    * `Witnesses/{Nat2, Nat3, Nat4}` — Nat-arity codomains
    * `Witnesses/Nat2Inj`          — Nat2 injectivity
    * `Witnesses/{Q213, Q213_3}`    — Q213 rational codomains
    * `Witnesses/Q213Inj`          — Q213 injectivity
    * `Witnesses/{Padding, PaddingCapstone}` — padding theorems
    * `Witnesses/TripleCapstone`   — triple-capstone integration

  Witnesses moved 2026-05-13 from `Meta/UniversalLens/` — LENS_AUDIT
  §4: Lens-content (not ring-independent Meta).
-/
