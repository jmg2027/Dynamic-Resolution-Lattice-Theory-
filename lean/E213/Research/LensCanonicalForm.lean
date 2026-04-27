import E213.Research.UniversalQuotLens
import E213.Research.KernelCongruence

/-!
# Research.LensCanonicalForm: Lens 의 canonical form via universalLens

`universalLens_recovers` (UniversalQuotLens.lean) 의 explicit
refines-equivalence wrapping.  framework 의 *self-stabilization*
의 형식 표현:

> 임의 Lens `M` 이 `universalLens M.equiv` 와 refines-equivalent.
>
> framework 가 자기 의 임의 Lens 를 자기 의 kernel 로 부터
> *up to refines-equivalence* 재구성.

## 의의

- `universalLens` 가 모든 Lens 의 canonical form.
- Lens 의 refines-equivalence class 가 slash-congruence 로
  parameterized.
- framework 가 자기 안 closure: Lens space 가 자기 의 quotient
  로 부터 reconstruct.

Note 78 분석.
-/

namespace E213.Research.LensCanonicalForm

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- **Lens refines-equivalence**: 두 Lens 가 같은 kernel. -/
def refinesEquiv {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  L.refines M ∧ M.refines L

theorem refinesEquiv_refl {α} (L : Lens α) : refinesEquiv L L :=
  ⟨Lens.refines_refl L, Lens.refines_refl L⟩

theorem refinesEquiv_symm {α β} {L : Lens α} {M : Lens β} :
    refinesEquiv L M → refinesEquiv M L
  | ⟨h1, h2⟩ => ⟨h2, h1⟩

end E213.Research.LensCanonicalForm

namespace E213.Research.LensCanonicalForm

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- **Self-stabilization**: 임의 Lens M 이 `universalLens M.equiv`
    와 refines-equivalent. -/
theorem lens_canonical_universal {α : Type} (M : Lens α)
    (hsym : ∀ u v, M.combine u v = M.combine v u) :
    refinesEquiv M (universalLens M.equiv) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    show (universalLens M.equiv).view x = (universalLens M.equiv).view y
    exact (universalLens_recovers α M hsym x y).mpr hxy
  · intro x y hxy
    show M.view x = M.view y
    exact (universalLens_recovers α M hsym x y).mp hxy

/-- **Idempotent canonical form**: universalLens 가 fixed-point. -/
theorem lens_canonical_idempotent {α : Type} (M : Lens α) :
    refinesEquiv (universalLens M.equiv)
                 (universalLens (universalLens M.equiv).equiv) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    show (universalLens (universalLens M.equiv).equiv).view x
         = (universalLens (universalLens M.equiv).equiv).view y
    exact (universalLens_idempotent α M x y).mpr hxy
  · intro x y hxy
    show (universalLens M.equiv).view x = (universalLens M.equiv).view y
    exact (universalLens_idempotent α M x y).mp hxy

end E213.Research.LensCanonicalForm
