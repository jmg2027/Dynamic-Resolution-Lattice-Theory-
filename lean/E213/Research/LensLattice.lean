import E213.Research.IdentityLens

/-!
# Research.LensLattice: Lens.refines 의 구조

`Lens.refines` (Hypervisor/Lens.lean) 는 Lens 들의 kernel 에
대한 preorder.  `L.refines M` iff `L.equiv` 이 `M.equiv` 보다
finer (L.ker ⊆ M.ker).

이 파일은 preorder 의 양 끝을 명시:

- **Bottom (finest kernel)**: `idLens` — equiv = `=` (Raw
  동등성).  모든 Lens 를 refine.
- **Top (coarsest kernel)**: `constLens e` — equiv = Raw × Raw
  (모두 같음).  모든 Lens 에 의해 refine 됨.

**따라서**: Lens L 의 view 가 injective ↔ L 이 idLens 를
refine 함 (L.ker ⊆ `=`).

## 의의

Note 34-36 의 diagonal 분석이 Lens 개별 data 에 대한 것이었
다면, 이 파일은 Lens **사이의 관계** 를 다룬다.  refines
preorder 가 Lens 세계의 구조를 제공.
-/

namespace E213.Research.LensLattice

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- Terminal Lens: 모든 Raw 를 한 점 e 로. -/
def constLens {α : Type} (e : α) : Lens α where
  base_a := e
  base_b := e
  combine _ _ := e

theorem constLens_view {α : Type} (e : α) (r : Raw) :
    (constLens e).view r = e := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : (constLens e).view (Raw.slash x y h)
                   = (constLens e).combine
                       ((constLens e).view x) ((constLens e).view y) :=
        Raw.fold_slash _ _ _ (by intro _ _; rfl) x y h
      rw [hfs]; rfl

end E213.Research.LensLattice

namespace E213.Research.LensLattice

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- **Bottom**: idLens 는 모든 Lens 를 refine.  idLens 의
    kernel 은 Raw 의 동등성 `=` 이므로 모든 kernel 에 포함. -/
theorem idLens_refines_all {α : Type} (L : Lens α) :
    idLens.refines L := by
  intro x y hxy
  have h : idLens.view x = idLens.view y := hxy
  rw [idLens_is_id, idLens_is_id] at h
  show L.view x = L.view y
  rw [h]

/-- **Top**: 모든 Lens 가 constLens e 를 refine.  constLens 의
    kernel 은 universal (모두 같음). -/
theorem all_refine_constLens {α : Type} (e : α) (L : Lens α) :
    L.refines (constLens e) := by
  intro x y _
  show (constLens e).view x = (constLens e).view y
  rw [constLens_view, constLens_view]

end E213.Research.LensLattice

namespace E213.Research.LensLattice

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- **Injectivity characterisation**: L 이 idLens 를 refine 함
    ↔ L.view 가 injective. -/
theorem refines_idLens_iff_injective {α : Type} (L : Lens α) :
    L.refines idLens ↔ Function.Injective L.view := by
  constructor
  · intro h x y hxy
    have hk : idLens.view x = idLens.view y := h x y hxy
    rw [idLens_is_id, idLens_is_id] at hk
    exact hk
  · intro hinj x y hxy
    have heq : x = y := hinj hxy
    show idLens.view x = idLens.view y
    rw [heq]

/-- constLens e 가 어떤 L 을 refine 하면 L 도 상수. -/
theorem constLens_refines_iff_const {α β : Type} (e : α) (L : Lens β) :
    (constLens e).refines L ↔ ∀ x y : Raw, L.view x = L.view y := by
  constructor
  · intro h x y
    apply h x y
    show (constLens e).view x = (constLens e).view y
    rw [constLens_view, constLens_view]
  · intro hconst x y _
    exact hconst x y

end E213.Research.LensLattice
