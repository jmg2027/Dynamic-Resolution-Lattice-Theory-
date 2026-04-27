import E213.Hypervisor.Lens

/-!
# Research.LensMorphism: Lens-algebra 간 morphism

Lens 는 α 위의 (base_a, base_b, combine) 데이터.  두 Lens
사이의 **morphism** 은 base 와 combine 을 보존하는 함수:

```
IsLensMorphism h L M :=
  h L.base_a = M.base_a ∧
  h L.base_b = M.base_b ∧
  ∀ u v, h (L.combine u v) = M.combine (h u) (h v)
```

**핵심 정리**: h 가 L-M morphism 이면 `M.view = h ∘ L.view`.
즉 Lens-morphism 이 view 수준에서 factoring 을 제공.

Note 39 의 `refines_of_factor` 가 generic factoring 이라면,
이 파일은 **algebraic structure 를 보존하는 factoring** 의
더 강한 form.
-/

namespace E213.Research.LensMorphism

open E213.Firmware E213.Hypervisor

/-- h 가 L-M Lens morphism. -/
def IsLensMorphism {α β : Type} (h : α → β) (L : Lens α) (M : Lens β) :
    Prop :=
  h L.base_a = M.base_a ∧
  h L.base_b = M.base_b ∧
  ∀ u v : α, h (L.combine u v) = M.combine (h u) (h v)

/-- **Factoring through morphism**: h 가 Lens morphism 이면
    `M.view r = h (L.view r)` for all r. -/
theorem view_factors_through_morphism {α β : Type}
    (L : Lens α) (M : Lens β) (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) :
    ∀ r : Raw, M.view r = h (L.view r) := by
  obtain ⟨hba, hbb, hcomb⟩ := hmor
  intro r
  induction r using Raw.rec with
  | a => show M.base_a = h L.base_a; exact hba.symm
  | b => show M.base_b = h L.base_b; exact hbb.symm
  | slash x y hxy ihx ihy =>
      have hfsM : M.view (Raw.slash x y hxy)
                    = M.combine (M.view x) (M.view y) :=
        Raw.fold_slash _ _ _ hMsym x y hxy
      have hfsL : L.view (Raw.slash x y hxy)
                    = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hLsym x y hxy
      rw [hfsM, hfsL, ihx, ihy, ← hcomb]

end E213.Research.LensMorphism

namespace E213.Research.LensMorphism

open E213.Firmware E213.Hypervisor

/-- **Morphism → Refinement**: h 가 L-M morphism 이면
    L.refines M (combine 대칭 하). -/
theorem refines_of_morphism {α β : Type} (L : Lens α) (M : Lens β)
    (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) : L.refines M := by
  intro x y hxy
  have hx : M.view x = h (L.view x) :=
    view_factors_through_morphism L M h hLsym hMsym hmor x
  have hy : M.view y = h (L.view y) :=
    view_factors_through_morphism L M h hLsym hMsym hmor y
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hx, hy, hxy']

end E213.Research.LensMorphism
