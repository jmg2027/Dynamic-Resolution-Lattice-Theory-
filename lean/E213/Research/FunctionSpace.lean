import E213.Research.SemanticAtom
import E213.Research.InstanceReach

/-!
# Research.FunctionSpace: function space `α → β` as a meaning-framework instance

`HasDistinguishing β → HasDistinguishing (α → β)` (with α inhabited).
Instance for function types — categorical exponential.

## Results

- `funHasDistinguishing α β [HasDistinguishing β] [Inhabited α]`:
  α → β is an instance.
- `universalMorphism (α → β)`: fold-derived Raw → (α → β).

A function type is also a framework instance — a trivial result
analogous to Lens.
-/

namespace E213.Research.FunctionSpace

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

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

end E213.Research.FunctionSpace

namespace E213.Research.FunctionSpace

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-- **Universal morphism Raw → (α → β)** via function-space instance.
    Elements of Raw are mapped to functions (α → β). -/
def funUniversalMorphism (α β : Type) [Inhabited α]
    [HasDistinguishing β] : Raw → (α → β) :=
  @universalMorphism (α → β) (funHasDistinguishing α β)

/-- **Concrete instance**: universal morphism for Bool → Bool. -/
def boolFunUniversal : Raw → (Bool → Bool) :=
  @funUniversalMorphism Bool Bool _ boolHasDistinguishing

end E213.Research.FunctionSpace
