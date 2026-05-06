import E213.Theory.Raw
import E213.Lens.LensCore
import E213.Lens.Characterisation.Catalog

/-!
# the two halves of R5, and which half is
formalisable on inductive Raw

Paper 1's R5 has two distinct components:

1. **Distinguishing:** every Raw term has a uniquely determined
   codomain state — i.e., `L.view` is injective.
2. **Completeness:** every *non-terminating structural branch*
   of Raw also has a uniquely determined state in the codomain.

Half (1) is the `Distinguishing` predicate in
`E213.Meta.LensCatalog`. It is **non-trivial**: swap-blind
Lenses (e.g. `Lens.leaves`) fail it, so the predicate has real
content.

Half (2) refers to objects **outside** the inductive Raw type:
infinite trajectories that are not themselves Raw terms (every
Raw term is finite by construction). Stating anything
universally about these infinite branches requires a
coinductive / classical ambient that is not supplied by the
axiom. In Lean 4 core with inductive Raw, half (2) is
**vacuously true** over the empty class of inductive
"non-terminating Raw terms".

Consequence for Paper 1 §4: the ℝ-algebra premise is supported
only by half (2), which is the part that cannot be formalised
inside the axiom's Raw. This is the smuggling channel.
-/

namespace E213.Lib.Math.CayleyDickson.R5Vacuity

open E213.Theory E213.Lens E213.Meta

/-- **Fold totality (R5' — finitist R5).** Every Raw term has
    a fully-determined Lens view. This is *automatic* for any
    Lens under inductive Raw, because `L.view` is a total
    function (built as a catamorphism). No `ring`, no
    `sorry`. -/
theorem foldTotality {α : Type} (L : Lens α) (r : Raw) :
    ∃ a : α, L.view r = a :=
  ⟨L.view r, rfl⟩

/-- Corollary: R5' places **no** constraint on the Lens. Any
    `Lens α` satisfies it. -/
theorem foldTotality_vacuous {α : Type} :
    ∀ L : Lens α, ∀ r : Raw, ∃ a : α, L.view r = a :=
  fun L r => foldTotality L r

end E213.Lib.Math.CayleyDickson.R5Vacuity
