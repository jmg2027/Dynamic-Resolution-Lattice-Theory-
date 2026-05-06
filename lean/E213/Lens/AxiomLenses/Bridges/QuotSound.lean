import E213.Lens.AxiomLenses.Core.QuotSound

/-!
# `AxiomLenses/Bridges/QuotSound.lean` — Lean ↔ 213 Quot.sound bridge

★ DIRTY-by-design.  This file's `sound_lens` deliberately applies
Lean's `Quot.sound` axiom to demonstrate that Quot.sound IS the
"equivalence-class collapse" lens application.  The DIRTY status
here is *the point*.

## Importing

213's core code MUST NOT import this file.  Only metatheoretic
demonstrations (showing the bridge between 213-native
`SetoidLens` and Lean's external quotient identity) may.

The `Core/QuotSound.lean` companion (PURE) provides the
213-internal-only API.
-/

namespace E213.Lens.AxiomLenses.Bridges.QuotSound

open E213.Lens.AxiomLenses.Core.QuotSound

/-- The Quot.sound lens: applying it collapses r-related elements
    into the same quotient point.  This is the rule that makes
    SetoidLens.quotient an actual quotient (not just data).

    DIRTY [Quot.sound] BY DESIGN. -/
theorem sound_lens {α : Type} (s : SetoidLens α) {a b : α}
    (h : s.rel a b) : project s a = project s b :=
  Quot.sound h

end E213.Lens.AxiomLenses.Bridges.QuotSound
