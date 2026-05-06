import E213.Lens.AxiomLenses.Bridges.Funext
import E213.Lens.AxiomLenses.Bridges.QuotSound

/-! Spec-as-code entry point for `E213.Lens.AxiomLenses.Bridges`.

  Bridges between the AxiomLenses Core witnesses (Funext,
  QuotSound) and the rest of the Lens algebra — i.e. how
  downstream constructions in `Lens/{Compose, Lattice, …}`
  invoke them, and what equational consequences follow.

  ## Files

    * `Funext`    — Funext bridge
    * `QuotSound` — Quot.sound bridge
-/
