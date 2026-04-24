import E213.Research.DiagonalClassification

/-!
# Research.IdempotentConstancy: Idempotent + swap-blind ⟹ constant

**정리**: `L : Lens α` 이 Idempotent 이고 `base_a = base_b`
(swap-blind) 이고 combine 이 대칭이면 `L.view` 는 상수 (=
`L.base_a`).

## 의의

idempotent combine 은 "같은 것끼리 합쳐도 변화 없음" 을 의미.
base 가 swap-blind 이면 모든 leaf 가 같은 값 → 모든 fold
값도 같은 값 (idempotent 유지).  view collapse.

이는 boolAndLens, boolOrLens 가 `view r = true` constant 인
이유를 일반화.  Note 35 의 Idempotent 범주와 Note 37 의
top-근처 (constant view Lens) 간 자연스러운 다리.
-/

namespace E213.Research.IdempotentConstancy

open E213.Firmware E213.Hypervisor E213.Research.DiagonalClassification

/-- **Idempotent + swap-blind base → constant view**. -/
theorem idempotent_swap_blind_const {α : Type} (L : Lens α)
    (hI : Idempotent L) (hbase : L.base_a = L.base_b)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u) :
    ∀ r : Raw, L.view r = L.base_a := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => exact hbase.symm
  | slash x y h ihx ihy =>
      have hfs : L.view (Raw.slash x y h)
                   = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hsym x y h
      rw [hfs, ihx, ihy]
      exact hI L.base_a

end E213.Research.IdempotentConstancy
