import E213.Lens.AxiomLenses.Core
import E213.Lens.AxiomLenses.Bridges

/-! Spec-as-code entry point for `E213.Lens.AxiomLenses`.

  Lean kernel axioms (Funext / Propext / QuotSound) formalised as
  Lens choices on Raw — see `AxiomLenses/INDEX.md`.

  **Bridges intentionally NOT bundled here.**  The DIRTY-by-design
  Lean-axiom bridges (`AxiomLenses/Bridges/{Funext, QuotSound}.lean`)
  must be imported **explicitly** by any consumer that uses them,
  to keep the strict ∅-axiom contract of 213 core enforceable at
  the import level.  Bare `import E213.Lens.AxiomLenses` and bare
  `import E213.Lens` give Core only.
-/
