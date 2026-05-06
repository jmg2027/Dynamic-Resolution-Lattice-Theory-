import E213.Hypervisor.Lens.AxiomLenses.Core.Funext
import E213.Hypervisor.Lens.AxiomLenses.Core.Propext
import E213.Hypervisor.Lens.AxiomLenses.Core.QuotSound

/-! Spec-as-code entry point for `E213.Hypervisor.Lens.AxiomLenses.Core`.

  Axiom-Lens core: each Lean 4 metatheory axiom (Funext / Propext
  / Quot.sound) is realised as a concrete Lens witness, exposing
  exactly which axiom each construction depends on.

  ## Files

    * `Funext`    — Funext axiom realisation
    * `Propext`   — Propext axiom realisation
    * `QuotSound` — Quot.sound axiom realisation
-/
