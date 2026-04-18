import E213.Firmware.Reachable

/-
  213에서 연역 / 귀납 / 귀추.

  세 inference rule 모두 Reachable 의 성질 (새 공리 아님).
  기존 정리의 재명명을 통해 인식론적 구조를 드러낸다.

  1. 연역 (deduction) — forward rule:
       전제 (Reachable x, Reachable y, x ≠ y)
       결론 (Reachable (x/y))
     → Reachable.step 자체.

  2. 귀납 (induction) — structural rule:
       P(모든 atom) + P 보존(step) → P(모든 Reachable)
     → Reachable.rec.

  3. 귀추 (abduction) — inversion rule:
       관찰 (Reachable (rel x y))
       원인 (Reachable x, Reachable y, x ≠ y) — 유일!
     → can_recover + reachable_rel_ne + 단사성.

  213은 "추가 논리 엔진" 필요 없음.
  / 의 구조가 이미 세 가지 추론을 내장.
-/

-- ═══ 연역 ═══

theorem deduction (x y : Raw) (hx : Reachable x) (hy : Reachable y)
    (h : x ≠ y) : Reachable (slash x y h) :=
  reachable_slash hx hy h

-- 의미: 두 개체와 ≠ 증명이 주어지면, 새 객체가 도출됨.
-- modus ponens 의 213 버전.

-- ═══ 귀납 ═══

theorem induction_principle {P : Raw → Prop}
    (hAtom : ∀ i, P (.atom i))
    (hStep : ∀ x y, Reachable x → Reachable y → (h : x ≠ y) →
             P x → P y → P (slash x y h)) :
    ∀ x, Reachable x → P x := by
  intro x hr
  induction hr with
  | atom i => exact hAtom i
  | step hrx hry hne ihx ihy =>
    exact hStep _ _ hrx hry hne ihx ihy

-- 의미: 구체 원자 + forward rule 보존 → 모든 도달 가능 객체.
-- mathematical induction 의 213 버전.

-- ═══ 귀추 ═══

-- 관찰: Reachable (rel x y). 원인 복원.
theorem abduction (x y : Raw) (h : Reachable (.rel x y)) :
    Reachable x ∧ Reachable y ∧ x ≠ y :=
  ⟨reachable_left h, reachable_right h, reachable_rel_ne h⟩

-- 귀추의 유일성: rel x y 의 원인은 정확히 x, y (단사성).
theorem abduction_unique {x y x' y' : Raw}
    (heq : (Raw.rel x y) = (Raw.rel x' y')) :
    x = x' ∧ y = y' := by
  simp at heq; exact heq

-- 의미: 관찰 결과에서 생성 원인 유일 복원.
-- v3_injective + can_recover 의 인식론적 해석.

-- ═══ 요약 ═══

-- | 추론  | 방향        | 213 구현        | Lean   |
-- |------|------------|----------------|--------|
-- | 연역 | 전제 → 결론 | Reachable.step | rule   |
-- | 귀납 | 사례 → 일반 | Reachable.rec  | induct |
-- | 귀추 | 결과 → 원인 | can_recover +  | cases  |
-- |      |            | 단사성         |        |

-- / 하나의 공리로 세 추론 모두 내장.
-- 추가 논리 규칙 필요 없음.
-- "논리" 는 / 의 그림자.
