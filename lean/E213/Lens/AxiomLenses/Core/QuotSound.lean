/-!
# `AxiomLenses/Core/QuotSound.lean` — quotSound213 (PURE 213-native Quot.sound analogue)

The 213-native form of "quotient soundness": equivalence as a
relation on raw data + a setoid structure that *carries* (not
*collapses*) the equivalence.  No appeal to Lean's `Quot.sound`.

## Usage

Anywhere 213 needs quotient-like behavior, use `SetoidLens` and
its `project` view; never appeal to `Quot.mk r a = Quot.mk r b`
forcing — instead show `s.rel a b` and reason about
`Lens.view r₁ = L.view r₂` directly.  This is the quotSound213
discipline.

The bridge to Lean's `Quot.sound` (showing the project of
related elements is propositionally equal) lives in
`AxiomLenses/Bridges/QuotSound.lean`.
-/

namespace E213.Lens.AxiomLenses.Core.QuotSound

/-- A setoid view: a type α with an equivalence relation `r`.
    This carries the equivalence WITHOUT collapsing it to identity. -/
structure SetoidLens (α : Type) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- The setoid's quotient type — Lean's `Quot` is one realisation. -/
def quotient {α : Type} (s : SetoidLens α) : Type := Quot s.rel

/-- The "view" projecting α onto its equivalence class. -/
def project {α : Type} (s : SetoidLens α) (a : α) : quotient s :=
  Quot.mk s.rel a

end E213.Lens.AxiomLenses.Core.QuotSound
