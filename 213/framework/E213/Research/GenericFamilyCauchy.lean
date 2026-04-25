import E213.Research.LensCauchy
import E213.Research.ABLens
import E213.Research.ArchimedeanCauchy
import E213.Research.ProfiniteSeq

/-!
# Research.GenericFamilyCauchy: Lens + post-processing 의 통합 framework

ArchimedeanCauchy (orderProj family) 와 ProfiniteSeq (mod m
family) 가 **같은 추상화 의 두 instance** 임을 명시.

## 통합 form

`(L, F) family-Cauchy` where L : Lens α, F : ι → α → β:

```
∀ i, ∃ N, ∀ k l ≥ N, F i (L.view (xs k)) = F i (L.view (xs l))
```

ι, β 는 임의 type.

- **Profinite case**: L = Lens.leaves, F m = (· % m), β = Nat.
- **Archimedean case**: L = abLens, F (m, k) = orderProj m k,
  β = Bool.

## 의의

Mingu (c)+(d): "Profinite ↔ Archimedean 둘 다 어떤 Lens family
선택 의 차이.  같은 limitLens 메커니즘".

이 file 이 그 통일 의 형식 표현.
-/

namespace E213.Research.GenericFamilyCauchy

open E213.Firmware E213.Hypervisor

/-- **Generic family-Cauchy**: Lens L 의 view 위 family of
    derived projections F 의 Cauchy. -/
def GFCauchy {α β : Type} {ι : Type} (L : Lens α) (F : ι → α → β)
    (xs : Nat → Raw) : Prop :=
  ∀ i, ∃ N, ∀ k l, k ≥ N → l ≥ N →
    F i (L.view (xs k)) = F i (L.view (xs l))

/-- **Generic Cauchy data**: explicit witness + post-processing. -/
structure GFCauchyData {α β : Type} {ι : Type}
    (L : Lens α) (F : ι → α → β) (xs : Nat → Raw) where
  N : ι → Nat
  cauchy : ∀ i k l, k ≥ N i → l ≥ N i →
    F i (L.view (xs k)) = F i (L.view (xs l))

/-- Limit assignment 추출. -/
def GFCauchyData.limitAssign {α β : Type} {ι : Type}
    {L : Lens α} {F : ι → α → β} {xs : Nat → Raw}
    (cd : GFCauchyData L F xs) : ι → β :=
  fun i => F i (L.view (xs (cd.N i)))

/-- Limit assignment 의 well-definedness. -/
theorem limitAssign_eq_tail {α β : Type} {ι : Type}
    {L : Lens α} {F : ι → α → β} {xs : Nat → Raw}
    (cd : GFCauchyData L F xs) (i : ι) (n : Nat) (hn : n ≥ cd.N i) :
    F i (L.view (xs n)) = cd.limitAssign i :=
  cd.cauchy i n (cd.N i) hn (Nat.le_refl _)

end E213.Research.GenericFamilyCauchy

namespace E213.Research.GenericFamilyCauchy

open E213.Firmware E213.Hypervisor
open E213.Research.LensCauchy

/-- **LensCauchy is GFCauchy instance** with trivial family
    (single Lens, identity post-processing). -/
theorem lensCauchy_is_GFCauchy {α : Type} (L : Lens α)
    (xs : Nat → Raw) (h : LensCauchy L xs) :
    GFCauchy L (fun (_ : Unit) (a : α) => a) xs := by
  intro _
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro k l hk hl
  exact hN k l hk hl

end E213.Research.GenericFamilyCauchy

namespace E213.Research.GenericFamilyCauchy

open E213.Firmware E213.Hypervisor

/-- **ArchimedeanCauchy is GFCauchy instance**: orderProj family
    + abLens 는 GFCauchy with ι = Nat × Nat, β = Bool. -/
theorem orderCauchy_is_GFCauchy
    (xs : Nat → Raw)
    (h : E213.Research.ArchimedeanCauchy.isOrderCauchy xs) :
    GFCauchy E213.Research.ABLens.abLens
      (fun (mk : Nat × Nat) (p : Nat × Nat) =>
         E213.Research.ArchimedeanCauchy.orderProj mk.1 mk.2 p) xs := by
  intro mk
  by_cases hk : mk.2 ≥ 1
  · obtain ⟨N, hN⟩ := h mk.1 mk.2 hk
    exact ⟨N, hN⟩
  · -- mk.2 = 0: orderProj 가 항상 true (since p.1 * 0 = 0 ≤ p.2 * mk.1)
    refine ⟨0, ?_⟩
    intro k l _ _
    show E213.Research.ArchimedeanCauchy.orderProj mk.1 mk.2 _ =
         E213.Research.ArchimedeanCauchy.orderProj mk.1 mk.2 _
    have hk0 : mk.2 = 0 := by omega
    unfold E213.Research.ArchimedeanCauchy.orderProj
    rw [hk0]
    simp

end E213.Research.GenericFamilyCauchy

namespace E213.Research.GenericFamilyCauchy

open E213.Firmware E213.Hypervisor

/-- **Profinite (factorial) Cauchy is GFCauchy instance**:
    Lens.leaves + (· % (m+1)) family.  Index 가 ℕ 인데 m+1 사용
    하여 m+1 ≥ 1 자동 보장. -/
theorem profinite_factorial_is_GFCauchy
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n)
                 = E213.Research.ProfiniteSeq.factorial (n + 1)) :
    GFCauchy Lens.leaves (fun (m : Nat) (n : Nat) => n % (m + 1)) xs := by
  intro m
  refine ⟨m + 1, ?_⟩
  intro k l hk hl
  show Lens.leaves.view (xs k) % (m + 1) = Lens.leaves.view (xs l) % (m + 1)
  rw [hLeaves k, hLeaves l]
  rw [E213.Research.ProfiniteSeq.factorial_eventually_zero_mod (m+1) (by omega) k (by omega),
      E213.Research.ProfiniteSeq.factorial_eventually_zero_mod (m+1) (by omega) l (by omega)]

end E213.Research.GenericFamilyCauchy
