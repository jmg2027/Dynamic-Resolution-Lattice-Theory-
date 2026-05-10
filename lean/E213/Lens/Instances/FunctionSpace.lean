import E213.Lens.SemanticAtom
import E213.Lens.Instances.Reach

/-!
# FunctionSpace: function space `α → β` as a meaning-framework instance

`HasDistinguishing β → HasDistinguishing (α → β)` (with α inhabited).
Instance for function types — categorical exponential.

## Results

- `funHasDistinguishing α β [HasDistinguishing β] [Inhabited α]`:
  α → β is an instance.
- `universalMorphism (α → β)`: fold-derived Raw → (α → β).

A function type is also a framework instance — a trivial result
analogous to Lens.
-/

namespace E213.Lens.Instances.FunctionSpace

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

/-- **Universal morphism Raw → (α → β)** — defined directly via
    `Raw.fold` on (a, b, combine) extracted from `HasDistinguishing β`.
    The function-space `combine_sym = ∀ f g, combine f g = combine g f`
    is funext-by-design at the function-eq level; we therefore do NOT
    construct a `HasDistinguishing (α → β)` instance and instead define
    the universal morphism directly.  ∅-axiom. -/
def funUniversalMorphism (α β : Type) [d_β : HasDistinguishing β] :
    Raw → (α → β) :=
  Raw.fold (fun _ => d_β.a) (fun _ => d_β.b)
           (fun f g x => d_β.combine (f x) (g x))

/-- **Concrete instance**: universal morphism for Bool → Bool. -/
def boolFunUniversal : Raw → (Bool → Bool) :=
  @funUniversalMorphism Bool Bool boolHasDistinguishing

end E213.Lens.Instances.FunctionSpace
