/-!
# E213.Prelude: tiny shims for standard definitions absent from
Lean 4 core (`Function.Injective`, `Surjective`, `Bijective`).

These live in `Function` namespace to match Mathlib naming — when
the project eventually depends on Mathlib, this file can be dropped
with no downstream changes.
-/

namespace Function

def Injective {α β : Sort _} (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂

def Surjective {α β : Sort _} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

def Bijective {α β : Sort _} (f : α → β) : Prop :=
  Injective f ∧ Surjective f

end Function
