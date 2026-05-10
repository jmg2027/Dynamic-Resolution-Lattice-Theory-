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

/-- HasDistinguishing instance for function space `α → β`.
    α is assumed to be inhabited (a witness element is needed
    to prove distinctness). -/
def funHasDistinguishing (α β : Type) [Inhabited α]
    [d_β : HasDistinguishing β] : HasDistinguishing (α → β) where
  a := fun _ => d_β.a
  b := fun _ => d_β.b
  distinct := by
    intro h
    have h_at : (fun _ : α => d_β.a) (default : α)
                = (fun _ : α => d_β.b) (default : α) :=
      congrFun h (default : α)
    exact d_β.distinct h_at
  combine := fun f g x => d_β.combine (f x) (g x)
  combine_sym := by
    intro f g
    funext x
    exact d_β.combine_sym _ _

end E213.Lens.Instances.FunctionSpace

namespace E213.Lens.Instances.FunctionSpace

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

/-- **Universal morphism Raw → (α → β)** — defined directly via
    `Raw.fold`, bypassing the DIRTY `funHasDistinguishing` typeclass
    (whose `combine_sym` field uses funext on the function-space).
    Definitionally equivalent to `@universalMorphism (α → β)
    (funHasDistinguishing α β)` but ∅-axiom. -/
def funUniversalMorphism (α β : Type) [d_β : HasDistinguishing β] :
    Raw → (α → β) :=
  Raw.fold (fun _ => d_β.a) (fun _ => d_β.b)
           (fun f g x => d_β.combine (f x) (g x))

/-- **Concrete instance**: universal morphism for Bool → Bool. -/
def boolFunUniversal : Raw → (Bool → Bool) :=
  @funUniversalMorphism Bool Bool boolHasDistinguishing

end E213.Lens.Instances.FunctionSpace
