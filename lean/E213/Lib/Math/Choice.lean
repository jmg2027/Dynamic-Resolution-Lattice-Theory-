import E213.Lib.Math.Choice.BootstrapWitness
import E213.Lib.Math.Choice.Canonical
import E213.Lib.Math.Choice.CanonicalTruthChar
import E213.Lib.Math.Choice.Resolved

/-! Spec-as-code entry point for `E213.Lib.Math.Choice`.

  Choice-related results — 213-native, no `Classical.choice`.

  ## Files

    * `Canonical`           — canonical-witness selector
                              (constructive, not Classical)
    * `CanonicalTruthChar`  — characterisation of canonical
                              truth value
    * `BootstrapWitness`    — bootstrap-style witness construction
    * `Resolved`            — resolved-decision-procedure
                              variant (Resolved Bool replacement
                              for Classical's excluded middle)
-/
