import E213.Lens.SemanticAtom
import E213.Lens.Instances.Reach

/-!
# FunctionSpace: function space `α → β` as a fold-target

`Raw.fold` directly produces `Raw → (α → β)` when `β` is a
distinguishing-framework instance.  The result is the categorical
exponential's universal morphism, PURE (∅-axiom).

## Results

- `funUniversalMorphism (α → β)`: fold-derived Raw → (α → β),
  computed via `Raw.fold` on `(fun _ => d_β.a, fun _ => d_β.b,
  pointwise d_β.combine)`.
- `boolFunUniversal : Raw → (Bool → Bool)` — concrete `Bool → Bool` case.

A typeclass instance `funHasDistinguishing : HasDistinguishing (α → β)`
would require `combine_sym` at function-equality type, demanding
`funext` (= `Quot.sound` in the Lean 4 kernel) — i.e. it would be
DIRTY.  We do not produce such an instance: the direct fold above
gives the universal morphism without typeclass machinery, keeping
the module ∅-axiom.
-/

namespace E213.Lens.Instances.FunctionSpace

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

/-- **Universal morphism Raw → (α → β)** — defined directly via
    `Raw.fold` on pointwise `combine`.  ∅-axiom. -/
def funUniversalMorphism (α β : Type) [d_β : HasDistinguishing β] :
    Raw → (α → β) :=
  Raw.fold (fun _ => d_β.a) (fun _ => d_β.b)
           (fun f g x => d_β.combine (f x) (g x))

/-- **Concrete instance**: universal morphism for Bool → Bool. -/
def boolFunUniversal : Raw → (Bool → Bool) :=
  @funUniversalMorphism Bool Bool boolHasDistinguishing

end E213.Lens.Instances.FunctionSpace

