/-!
# `AxiomLenses/Core/Funext.lean` — funext213 (PURE 213-native funext analogue)

The 213-native form of "function extensionality": pointwise
equality as a relation on the function space.  No appeal to
Lean's `funext` (which would drag in `Quot.sound`).

## Usage

Anywhere 213 needs to express "two functions are equal", state the
goal as `pointwiseEq f g` instead of `f = g`.  This is the
funext213 discipline — strict ∅-axiom across the entire 213 core.

The Lean-bridge (the actual axiom application showing pointwise
eq → Lean's `=`) lives in `AxiomLenses/Bridges/Funext.lean`.
-/

namespace E213.Hypervisor.AxiomLenses.Core.Funext

/-- The funext-lens equivalence: two functions agree iff they
    have the same value at every input.  This is the 213-native
    funext analogue (funext213). -/
def pointwiseEq {α β : Type} (f g : α → β) : Prop :=
  ∀ x, f x = g x

theorem pointwiseEq_refl {α β : Type} (f : α → β) : pointwiseEq f f :=
  fun _ => rfl

theorem pointwiseEq_symm {α β : Type} {f g : α → β}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun x => (h x).symm

theorem pointwiseEq_trans {α β : Type} {f g h : α → β}
    (hfg : pointwiseEq f g) (hgh : pointwiseEq g h) : pointwiseEq f h :=
  fun x => (hfg x).trans (hgh x)

/-- The trivial direction (Eq → pointwise eq) is constructive. -/
theorem eq_implies_pointwiseEq {α β : Type} {f g : α → β} (h : f = g) :
    pointwiseEq f g := fun x => h ▸ rfl

/-- The non-trivial direction (pointwise eq → Eq) IS funext.
    Stated here as a *type-level claim*; the actual axiomatic
    inhabitant lives in `AxiomLenses/Bridges/Funext.lean`. -/
abbrev funextLens {α β : Type} (f g : α → β) : Prop :=
  pointwiseEq f g → f = g

end E213.Hypervisor.AxiomLenses.Core.Funext
