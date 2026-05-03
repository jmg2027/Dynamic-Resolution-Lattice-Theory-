import E213.Hypervisor.Lens.AxiomLenses.Core.Funext

/-!
# `AxiomLenses/Bridges/Funext.lean` — Lean ↔ 213 funext bridge

★ DIRTY-by-design.  This file's `funextLens_inhabited` deliberately
applies Lean's `funext` axiom to demonstrate that funext IS the
"pointwise-eq → Eq" lens application.  The DIRTY status here is
*the point*.

## Importing

213's core code MUST NOT import this file.  Only metatheoretic
demonstrations (showing the bridge between 213-native
`pointwiseEq` and Lean's external function-equality) may.

The `Core/Funext.lean` companion (PURE) provides the
213-internal-only API.
-/

namespace E213.Hypervisor.Lens.AxiomLenses.Bridges.Funext

open E213.Hypervisor.Lens.AxiomLenses.Core.Funext

/-- Lean 4 provides this lens for every (α, β, f, g) via Quot.sound.
    The 213-strict-∅-axiom standard says: "we don't apply this lens
    by default; use it only at explicit boundaries."

    DIRTY [Quot.sound] BY DESIGN. -/
theorem funextLens_inhabited {α β : Type} (f g : α → β) :
    funextLens f g := funext

end E213.Hypervisor.Lens.AxiomLenses.Bridges.Funext
