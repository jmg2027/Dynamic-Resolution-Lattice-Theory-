import E213.Hypervisor.Lens
import E213.Prelude

/-!
# Research.IdentityLens: Raw → Raw 항등 Lens + Yoneda-dual

Note 34 Q34.4 의 부분 답.

**Self-encoding 은 불가** — Lens α 는 α 에 의존하므로 "모든
α 에 대한 canonical `Lens.fromRaw : Raw → Lens α`" 는 없음.

**하지만 dual 은 자연스러움** — 각 Raw 원소 r 은 모든 Lens
를 평가하는 함수:

```
Raw.eval r {α} (L : Lens α) : α := L.view r
```

이 dual 은 `Lens.view L : Raw → α` 를 Raw 쪽에서 본 형태.

- §1. **identity Lens `idLens : Lens Raw`** — Q34.3 의 가장
  단순한 구현 (codomain = Raw).
- §2. injective Lens witness.  `r ↦ Raw.eval r idLens` 는
  injective.
-/

namespace E213.Research.IdentityLens

open E213.Firmware E213.Hypervisor

/-- Identity Lens: view = id on Raw.  combine 은 Raw.slash
    (x ≠ y 분기), 대각에서는 fallback Raw.a — 대각은 view
    계산 중 hit 되지 않음 (slash 분기의 `x ≠ y` 보장). -/
def idLens : Lens Raw where
  base_a := Raw.a
  base_b := Raw.b
  combine x y := if h : x ≠ y then Raw.slash x y h else Raw.a

theorem idLens_symmetric :
    ∀ u v : Raw, idLens.combine u v = idLens.combine v u := by
  intro u v
  by_cases h : u = v
  · rw [h]
  · show (if h : u ≠ v then Raw.slash u v h else Raw.a)
         = (if h : v ≠ u then Raw.slash v u h else Raw.a)
    rw [dif_pos h, dif_pos (Ne.symm h)]
    exact Raw.slash_comm u v h

end E213.Research.IdentityLens

namespace E213.Research.IdentityLens

open E213.Firmware E213.Hypervisor

theorem idLens_is_id : ∀ r : Raw, idLens.view r = r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : idLens.view (Raw.slash x y h)
                   = idLens.combine (idLens.view x) (idLens.view y) :=
        Raw.fold_slash idLens.base_a idLens.base_b idLens.combine
          idLens_symmetric x y h
      rw [hfs, ihx, ihy]
      show (if h' : x ≠ y then Raw.slash x y h' else Raw.a)
           = Raw.slash x y h
      rw [dif_pos h]

end E213.Research.IdentityLens

namespace E213.Research.IdentityLens

open E213.Firmware E213.Hypervisor

/-- `idLens.view` 는 injective (실은 identity). -/
theorem idLens_injective : Function.Injective idLens.view := by
  intro x y hxy
  rw [idLens_is_id x, idLens_is_id y] at hxy
  exact hxy

/-- **Yoneda-dual**: Raw 원소 r 이 모든 Lens α 를 평가하는
    함수.  `L.view : Raw → α` 의 dual 시점. -/
def Raw.eval (r : Raw) {α : Type} (L : Lens α) : α := L.view r

/-- `r ↦ Raw.eval r idLens` 는 injective.  즉 Raw 원소는
    Lens-evaluator 로서 서로 구분됨. -/
theorem raw_distinguished_by_idLens :
    Function.Injective (fun r : Raw => Raw.eval r idLens) :=
  idLens_injective

end E213.Research.IdentityLens
