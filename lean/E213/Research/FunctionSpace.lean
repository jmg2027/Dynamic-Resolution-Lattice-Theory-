import E213.Research.SemanticAtom
import E213.Research.InstanceReach

/-!
# Research.FunctionSpace: function space `α → β` 도 의미 framework instance

`HasDistinguishing β → HasDistinguishing (α → β)` (with α inhabited).
function type 의 instance — categorical exponential.

## 결과

- `funHasDistinguishing α β [HasDistinguishing β] [Inhabited α]`:
  α → β 가 instance.
- `universalMorphism (α → β)`: Raw → (α → β) 의 fold-derived.

functional type 도 framework 의 instance — Lens 와 비슷 한 자명
한 결과.
-/

namespace E213.Research.FunctionSpace

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom
open E213.Research.InstanceReach

/-- Function space `α → β` 의 HasDistinguishing instance.
    α 는 inhabited 가정 (witness 한 element 가 있어 distinct
    proof 가능). -/
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
    Raw 의 element 가 함수 (α → β) 로 mapping. -/
def funUniversalMorphism (α β : Type) [Inhabited α]
    [HasDistinguishing β] : Raw → (α → β) :=
  @universalMorphism (α → β) (funHasDistinguishing α β)

/-- **Concrete instance**: Bool → Bool 의 universal morphism. -/
def boolFunUniversal : Raw → (Bool → Bool) :=
  @funUniversalMorphism Bool Bool _ boolHasDistinguishing

end E213.Research.FunctionSpace
