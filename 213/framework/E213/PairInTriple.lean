import E213.Axiom
import E213.Closure

/-
  pair ⊂ triple: 213의 구조 정리.
  C(2,2)=1 (pair 붕괴). C(3,2)=3 (triple 자기유지).
  pair는 독립 존재 불가. 반드시 triple 안에 있음.
  이것이 골드바흐의 213 증명 뼈대.
-/

-- ═══ 추상 정리: 모든 pair는 triple 안에 있다 ═══

-- Obj에서: mul(a,b) = pair. 이것은 Generated.
-- 이 pair를 포함하는 triple이 항상 존재.

theorem pair_in_triple :
    ∀ (a b : Obj), ∃ (c : Obj),
      Generated (.mul a b) ∧
      Generated (.mul a c) ∧
      Generated (.mul b c) := by
  intro a b
  exact ⟨.gen 0,
    ⟨.step (all_generated a) (all_generated b),
     .step (all_generated a) (.base 0),
     .step (all_generated b) (.base 0)⟩⟩

-- 해석: pair (a,b)에 대해 c=gen 0이 witness.
-- (a,b), (a,c), (b,c) 세 비교 모두 Generated.
-- triple이 완성됨. C(3,2)=3.

-- ═══ 더 강한 버전: c도 제약 가능 ═══

-- 임의의 Obj를 c로 쓸 수 있음 (all_generated).
theorem pair_in_any_triple :
    ∀ (a b c : Obj),
      Generated (.mul a b) ∧
      Generated (.mul a c) ∧
      Generated (.mul b c) :=
  fun a b c =>
    ⟨.step (all_generated a) (all_generated b),
     .step (all_generated a) (all_generated c),
     .step (all_generated b) (all_generated c)⟩

-- ═══ 골드바흐 연결 ═══

-- 추상: 모든 pair는 triple 안에 있다. ✓ 증명됨.
-- 수학: "소수 pair는 소수 triple 안에 있는가?"
-- gap: "소수"라는 제약이 Obj에 없음.

-- 하지만 213이 말하는 것:
-- pair가 독립 존재 불가 = C(2,2)=1 = 자기유지 실패.
-- 이것은 "소수"와 무관한 구조적 사실.
-- 소수이든 아니든, pair는 triple 없이 자기유지 안 됨.

-- 수학적 번역:
-- "n = p+q (두 소수의 합)"은 pair 주장.
-- pair가 존재하려면 triple이 있어야 함.
-- triple = "세 소수 구조" = Vinogradov 유형.
-- Vinogradov가 증명됨 → triple 존재 보장.
-- triple 안에 pair 있음 → pair 존재 보장???

-- 문제: Vinogradov의 triple이 Goldbach의 pair를 포함하는가?
-- V: 큰 홀수 N = p₁+p₂+p₃.
-- G: 짝수 n = p+q.
-- n과 N의 관계: N = n-3 (홀수). n = N+3.
-- V → n-3 = p₁+p₂+p₃ → n = 3+p₁+p₂+p₃.
-- 이건 4소수 분해 (Goldbach는 2소수 필요).

-- 직접 연결은 안 됨. 하지만 구조적으로:
-- V의 triple이 존재한다는 사실이
-- pair의 "환경"을 보장.

-- ═══ 남은 것 ═══

-- "triple이 pair를 결정한다"를 소수에 대해 증명.
-- 추상: pair_in_triple (증명됨).
-- 소수: ??? (이것이 Goldbach의 실질적 내용).
