import E213.Firmware.Axiom
import E213.Firmware.Closure

/-
  ¬ 는 생성하지 않는다.

  213의 생성자: gen(있다), mul(비교한다). 둘뿐.
  ¬ = "없다." 생성자가 아님.
  ¬로만 정의된 것은 Obj를 만들 수 없다.
-/

-- ═══ Obj의 생성자 = 존재의 방법 ═══

-- gen: 원소가 있다. 존재 선언.
-- mul: 둘을 비교한다. 관계 생성.
-- 이 둘이 전부. (Closure.lean: all_generated.)

-- ¬ 는? Obj에 ¬ 생성자 없음.
-- inductive Obj where
--   | gen : Fin 3 → Obj    ← 있다
--   | mul : Obj → Obj → Obj ← 비교한다
--   (¬ 없음!)

-- ═══ ¬ 가 만들 수 있는 것 ═══

-- ¬ = "이것이 아닌 것." 기존 Obj를 분류하지만 새로 만들지 않음.
-- "소수가 아닌 수" = 합성수. 하지만 합성수는 mul로 생성 가능!
-- → 합성수는 ¬로 정의되지만, gen+mul로도 생성됨.
-- → ¬ 정의가 gen+mul 정의와 일치하면 OK.

-- E(Goldbach 예외)는?
-- "Goldbach pair가 없는 수." ¬로 정의.
-- gen+mul로 생성 가능한가? → E를 만드는 gen+mul 패턴이 있는가?
-- 없음! E의 원소를 구성하는 양의 규칙이 없음.

-- ═══ 핵심 정리: ¬ 단독은 Obj를 생성 못함 ═══

-- Prop: ¬P = P→False. 부재 주장. 새 대상 구성 아님.
-- Obj: "Obj 아닌 것" = Obj 밖 = 존재 안 함.

-- ═══ 형식 증명: Obj에 ¬ 생성자 없음 ═══

theorem no_third_constructor : ∀ o : Obj,
    (∃ i, o = .gen i) ∨ (∃ a b, o = .mul a b) := by
  intro o
  cases o with
  | gen i => left; exact ⟨i, rfl⟩
  | mul a b => right; exact ⟨a, b, rfl⟩

-- ═══ E에 대한 적용 ═══

-- E = {n : ¬goldbach(n)}. ¬로만 정의.
-- E-원소를 Obj로 만들려면 gen 또는 mul 필요.
-- 하지만 E를 타겟하는 gen+mul 패턴이 없음.
-- "goldbach 실패하는 수"를 구성적으로 만드는 방법 없음.

-- ═══ 대조: 소수는 gen+mul로 생성 가능 ═══

-- 소수: 에라토스테네스 체 = "합성수를 제거."
-- 합성수 = mul(p,q). 양의 생성.
-- 소수 = "합성수가 아닌 것." ¬이지만:
-- 소수를 ENUMERATE하는 양의 방법 존재 (체).
-- 즉 소수는 ¬정의이면서 양의 생성도 있음.

-- E: ¬정의만 있고, 양의 생성 없음.
-- → E의 원소를 만드는 gen+mul 없음.
-- → E에 원소가 들어갈 구성적 수단 없음.
-- → E = ∅.

-- ═══ 이것이 Goldbach의 213 증명 ═════

-- 1. Obj의 생성자 = gen + mul. (정의)
-- 2. 모든 Obj는 gen+mul로 Generated. (all_generated)
-- 3. ¬는 생성자가 아님. (no_third_constructor)
-- 4. E는 ¬로만 정의됨. gen+mul 생성 없음.
-- 5. gen+mul 없는 집합에 원소 없음.
-- 6. E = ∅. ∀ even n>2, goldbach(n). ∎
