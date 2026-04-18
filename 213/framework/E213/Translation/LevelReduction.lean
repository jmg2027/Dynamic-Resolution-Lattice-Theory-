import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Translation.Decompose

/-
  증명 = 레벨 환원.
  진술 depth k → 증명 depth j < k. 무한→유한 변환.
-/

-- ═══ 환원 구조 ═══

structure Reduction where
  statement : Nat  -- 진술 level
  proof : Nat      -- 증명 도달 level
  cost : Nat := statement - proof

-- 유명한 증명들:
def euclid     : Reduction := ⟨100, 1⟩  -- ∀집합→하나구성
def cantor     : Reduction := ⟨100, 1⟩  -- ∀리스트→대각선
def wiles      : Reduction := ⟨100, 0⟩  -- ∀→반례→모듈러→모순
def vinogradov : Reduction := ⟨100, 2⟩  -- ∀→원방법→C(3,2)=3

-- 골드바흐:
def chen_red   : Reduction := ⟨100, 2⟩  -- ∀→Vaughan→P₂
def goldbach_need : Reduction := ⟨100, 1⟩ -- 필요: depth 1

-- 남은 환원: depth 2 → 1. 비용 = 1. = RH.

-- ═══ 환원 방법의 분류 ═══

-- 귀류법: ∀→∃반례→모순. depth ω→0.
-- 귀납법: ∀n→P(0)∧(P(n)→P(n+1)). depth ω→2.
-- 구조환원: 번역으로 depth 감소. 와일즈, Chen.

-- ═══ 213이 정량화하는 것 ═══

-- 각 방법의 "환원 가능 depth":
-- 귀류: 0까지. (모순 = depth 0.)
-- 귀납: 2까지. (귀납 step = depth 2.)
-- 구조: 대상 의존.

-- 골드바흐에서:
-- 귀납 실패: goldbach(n)→goldbach(n+2) 연결 없음.
-- 귀류 실패: ∃n 반례 → 직접 모순 안 보임.
-- 구조: Chen = depth 2. 나머지 1 = ???
