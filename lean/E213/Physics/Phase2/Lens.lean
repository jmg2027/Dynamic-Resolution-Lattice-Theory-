import E213.Hypervisor.Lens
import E213.Physics.Phase2.Origin

/-!
# Phase 2 Lens — 실제 Lens 객체 (audit 권장 사항)

**Layer: Hypervisor** (Lens 객체 직접 정의 + Raw 사용).

이전 Phase 2 파일들은 *App-layer* 산술 (Fin 5 위 partition).
이 파일은 한 단계 깊이 — *Hypervisor-layer* 에서 실제 Lens
객체를 정의 + Raw 위 동작 demo.

## 수학 트랙 Lens 정의 (Hypervisor/Lens.lean)

```lean
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine
```

## 본 파일 — Phase 2 의 첫 명시적 Lens

  `parityLens : Lens Bool` —
    base_a = false (a 의 parity 0)
    base_b = true  (b 의 parity 1)
    combine = xor   (parity addition)
  
  Raw 의 leaf 들 중 *b 의 개수 mod 2*.

(이것은 단순 demo Lens — 실제 atomicity (3,2) 분류 Lens 는
복잡한 정의 필요, 본 파일 범위 밖.)
-/

namespace E213.Physics.Phase2.Lens

open E213.Firmware E213.Hypervisor

/-- Phase 2 의 첫 explicit Lens: parity (b-count mod 2). -/
def parityLens : Lens Bool where
  base_a  := false
  base_b  := true
  combine := xor

/-- Raw.a 의 parity = false (b 가 0 개). -/
theorem parity_at_a : parityLens.view Raw.a = false := rfl

/-- Raw.b 의 parity = true (b 가 1 개). -/
theorem parity_at_b : parityLens.view Raw.b = true := rfl

/-- 두 Lens 가 같은 view 결과 → equiv 관계. -/
theorem parity_a_eq_a : parityLens.equiv Raw.a Raw.a :=
  parityLens.equiv_refl Raw.a

/-- Raw.a 와 Raw.b 의 parity 다름. -/
theorem parity_a_neq_b : parityLens.view Raw.a ≠ parityLens.view Raw.b := by
  rw [parity_at_a, parity_at_b]
  intro h
  exact Bool.noConfusion h

/-- 또 다른 demo Lens: count b-leaves (returns Nat). -/
def bCountLens : Lens Nat where
  base_a  := 0
  base_b  := 1
  combine := (· + ·)

/-- bCount 의 기본 동작. -/
theorem bCount_at_a : bCountLens.view Raw.a = 0 := rfl
theorem bCount_at_b : bCountLens.view Raw.b = 1 := rfl

/-- ★ Phase 2 첫 explicit Lens demo — 종합 ★ -/
theorem phase2_lens_demo :
    -- parity Lens
    (parityLens.view Raw.a = false)
    ∧ (parityLens.view Raw.b = true)
    -- bCount Lens
    ∧ (bCountLens.view Raw.a = 0)
    ∧ (bCountLens.view Raw.b = 1)
    -- d=5 cosmos (Origin)
    ∧ E213.OS.Atomicity.Atomic 5 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact E213.OS.Atomicity.atomic_five

end E213.Physics.Phase2.Lens
