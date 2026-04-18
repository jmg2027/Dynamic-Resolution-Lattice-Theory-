import E213.Firmware.Properties

/-
  Reachable의 특성화.

  "진짜 존재하는 것" = 자연 전개로 도달 가능한 것.
  문제: Raw 타입에는 rel x x 같은 "유령"도 있음.
  해결: Reachable을 wellFormed로 특성화 → 판정 가능.

  핵심 정리:
    Reachable x ↔ wellFormed x
  그리고:
    wellFormed는 decidable → Reachable도 decidable.
-/

-- ═══ wellFormed: 구문적 조건 ═══

-- 트리의 모든 rel 노드에서 좌우가 다름. 재귀적으로.
def Raw.wellFormed : Raw → Prop
  | .atom _     => True
  | .rel x y    => x ≠ y ∧ x.wellFormed ∧ y.wellFormed

-- wellFormed는 판정 가능 (Raw가 DecidableEq이므로).
instance : DecidablePred Raw.wellFormed := by
  intro x
  induction x with
  | atom i => exact isTrue trivial
  | rel a b iha ihb =>
    simp [Raw.wellFormed]
    exact instDecidableAnd

-- ═══ 특성화 정리 ═══

-- (←) wellFormed면 도달 가능:
theorem reachable_of_wellFormed : ∀ x : Raw, x.wellFormed → Reachable x
  | .atom i,   _ => .atom i
  | .rel a b, h =>
      let ⟨hne, ha, hb⟩ := h
      .step (reachable_of_wellFormed a ha)
            (reachable_of_wellFormed b hb)
            hne

-- (→) 도달 가능하면 wellFormed:
theorem wellFormed_of_reachable {x : Raw} (h : Reachable x) : x.wellFormed := by
  induction h with
  | atom _ => exact trivial
  | step _ _ hne ihx ihy =>
    refine ⟨hne, ihx, ihy⟩

-- 양방향:
theorem reachable_iff_wellFormed (x : Raw) :
    Reachable x ↔ x.wellFormed :=
  ⟨wellFormed_of_reachable, reachable_of_wellFormed x⟩

-- ═══ 따름정리: Reachable은 판정 가능 ═══

instance : DecidablePred Reachable := fun x =>
  decidable_of_iff x.wellFormed (reachable_iff_wellFormed x).symm

-- 예시: 실제로 계산됨.
example : Reachable ab₀ := by decide
example : Reachable aab₀ := by decide
example : ¬ Reachable (.rel a₀ a₀) := by decide
example : ¬ Reachable (.rel ab₀ ab₀) := by decide

-- ═══ Reachable의 핵심 성질들 ═══

-- 1. rel x x는 절대 Reachable이 아니다 (유령).
theorem no_self_rel_reachable (x : Raw) : ¬ Reachable (.rel x x) := by
  rw [reachable_iff_wellFormed]
  simp [Raw.wellFormed]

-- 2. Reachable (rel x y) → x ≠ y (필연).
theorem reachable_rel_ne {x y : Raw} (h : Reachable (.rel x y)) : x ≠ y := by
  rw [reachable_iff_wellFormed] at h
  exact h.1

-- 3. 부분구조 닫힘: 왼쪽.
theorem reachable_left {x y : Raw} (h : Reachable (.rel x y)) : Reachable x := by
  rw [reachable_iff_wellFormed] at *
  exact h.2.1

-- 4. 부분구조 닫힘: 오른쪽.
theorem reachable_right {x y : Raw} (h : Reachable (.rel x y)) : Reachable y := by
  rw [reachable_iff_wellFormed] at *
  exact h.2.2

-- 5. slash 닫힘: Reachable끼리 / 하면 Reachable.
theorem reachable_slash {x y : Raw} (hx : Reachable x) (hy : Reachable y)
    (h : x ≠ y) : Reachable (slash x y h) :=
  .step hx hy h

-- ═══ Level: 깊이별 열거 ═══

-- 주어진 리스트의 서로 다른 쌍에 slash 적용.
def expandOne (L : List Raw) : List Raw :=
  L.flatMap fun x =>
    L.filterMap fun y =>
      if h : x ≠ y then some (slash x y h) else none

-- Level n까지 자연 전개 (seed: 3개 원자).
def levelUpTo : Nat → List Raw
  | 0     => [.atom 0, .atom 1, .atom 2]
  | n + 1 =>
    let prev := levelUpTo n
    (prev ++ expandOne prev).dedup

-- Level 0: 원자 3개.
example : (levelUpTo 0).length = 3 := by decide

-- Level 0의 모든 원소는 Reachable.
example : ∀ x ∈ levelUpTo 0, Reachable x := by decide

-- Level 1: 3 + C(3,2)×2 = 3 + 6 = 9 (ordered pairs).
example : (levelUpTo 1).length = 9 := by decide

-- Level 1의 모든 원소도 Reachable.
example : ∀ x ∈ levelUpTo 1, Reachable x := by decide

-- 주의: 여기서는 3개 원자(Fin 3 전체)를 seed로 씀.
-- ARCHITECTURE.md의 "Level 0: a, b, a/b (3개)"는 2 atoms seed.
-- 같은 재귀 구조, 다른 초기 조건.

-- ═══ 요약 ═══
-- 1. Reachable ↔ wellFormed (구문적 판정).
-- 2. Reachable은 DecidablePred.
-- 3. rel x x는 Raw에 있지만 Reachable 아님 (유령 확정).
-- 4. slash는 Reachable을 보존.
-- 5. levelUpTo n은 계산 가능.
