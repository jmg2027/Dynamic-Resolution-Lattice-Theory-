import E213.Hypervisor.Lens

/-!
# Research.LensFactoring: refines 의 general sufficient condition

**주장**: L.view 를 통해 M.view 가 factor 되면 L.refines M.

```
M.view = g ∘ L.view for some g : α → β  ⟹  L.refines M
```

이는 "M 은 L 이 주는 정보만 쓴다" 의 형식화.  모든 catalogue
refines relationship (note 38 §7 Q37.2) 의 **통일 도구**.

역방향은 비건설적 (AC 필요).  이 파일은 건설적 방향만 제공.
-/

namespace E213.Research.LensFactoring

open E213.Firmware E213.Hypervisor

/-- **Factoring → Refinement**: M.view 가 L.view 를 통해
    factor 되면 L.refines M. -/
theorem refines_of_factor {α β : Type} (L : Lens α) (M : Lens β)
    (g : α → β) (hfactor : ∀ r : Raw, M.view r = g (L.view r)) :
    L.refines M := by
  intro x y hxy
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hfactor x, hfactor y, hxy']

end E213.Research.LensFactoring
