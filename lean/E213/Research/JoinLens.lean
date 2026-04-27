import E213.Research.JoinEquiv
import E213.Research.UniversalQuotLens

/-!
# Research.JoinLens: 임의 Lens 쌍 의 concrete join Lens

`joinLens L M : Lens (Raw → Prop)` := `universalLens (JoinEquiv L M)`.

`JoinEquiv` 의 universal property + `universalLens_kernel_eq_E`
의 결합 으로 임의 Lens 쌍 에 대해 **concrete join Lens** 존재.

prodLens (meet) 와 함께 refines preorder 의 lattice 구조 완성.

## 핵심 정리

- `joinLens_kernel`: kernel of joinLens L M = JoinEquiv L M.
- `L_refines_joinLens`, `M_refines_joinLens`: upper bound 성.
- `joinLens_is_least`: least upper bound (universal property).
-/

namespace E213.Research.JoinLens

open E213.Firmware E213.Hypervisor
open E213.Research.JoinEquiv E213.Research.UniversalQuotLens

/-- JoinEquiv L M 은 equivalence relation. -/
private theorem joinEquiv_refl {α β : Type} (L : Lens α) (M : Lens β)
    (r : Raw) : JoinEquiv L M r r := JoinEquiv.refl r

private theorem joinEquiv_symm {α β : Type} (L : Lens α) (M : Lens β)
    (r r' : Raw) (h : JoinEquiv L M r r') : JoinEquiv L M r' r :=
  JoinEquiv.symm h

private theorem joinEquiv_trans {α β : Type} (L : Lens α) (M : Lens β)
    (r r' r'' : Raw)
    (h1 : JoinEquiv L M r r') (h2 : JoinEquiv L M r' r'') :
    JoinEquiv L M r r'' :=
  JoinEquiv.trans h1 h2

private theorem joinEquiv_slash {α β : Type} (L : Lens α) (M : Lens β)
    (x x' y y' : Raw) (h : x ≠ y) (h' : x' ≠ y')
    (hxx' : JoinEquiv L M x x') (hyy' : JoinEquiv L M y y') :
    JoinEquiv L M (Raw.slash x y h) (Raw.slash x' y' h') :=
  JoinEquiv.slash_cong h h' hxx' hyy'

/-- **Concrete join Lens**: 임의 Lens 쌍 의 join 을 universalLens
    구성 으로 명시. -/
def joinLens {α β : Type} (L : Lens α) (M : Lens β) : Lens (Raw → Prop) :=
  universalLens (JoinEquiv L M)

/-- **kernel = JoinEquiv**.  universalLens 의 직접 귀결. -/
theorem joinLens_kernel {α β : Type} (L : Lens α) (M : Lens β)
    (r r' : Raw) :
    (joinLens L M).view r = (joinLens L M).view r'
      ↔ JoinEquiv L M r r' := by
  apply universalLens_kernel_eq_E
  · exact joinEquiv_refl L M
  · exact joinEquiv_symm L M
  · exact joinEquiv_trans L M
  · exact joinEquiv_slash L M

/-- **L 이 joinLens L M 을 refine** (upper bound). -/
theorem L_refines_joinLens {α β : Type} (L : Lens α) (M : Lens β) :
    L.refines (joinLens L M) := by
  intro r r' h
  show (joinLens L M).view r = (joinLens L M).view r'
  rw [joinLens_kernel L M r r']
  exact JoinEquiv.ofL h

/-- **M 이 joinLens L M 을 refine** (upper bound). -/
theorem M_refines_joinLens {α β : Type} (L : Lens α) (M : Lens β) :
    M.refines (joinLens L M) := by
  intro r r' h
  show (joinLens L M).view r = (joinLens L M).view r'
  rw [joinLens_kernel L M r r']
  exact JoinEquiv.ofM h

/-- **Universal property**: joinLens L M 이 least upper bound.
    임의 N (combine sym) 에 대해 L, M 둘 다 refine 하면 joinLens
    이 N 도 refine. -/
theorem joinLens_is_least {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLN : L.refines N) (hMN : M.refines N) :
    (joinLens L M).refines N := by
  intro r r' h
  have hJE : JoinEquiv L M r r' := (joinLens_kernel L M r r').mp h
  exact JoinEquiv_is_least L M N hNsym hLN hMN r r' hJE

end E213.Research.JoinLens
