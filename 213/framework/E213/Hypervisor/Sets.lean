import E213.Axiom
import E213.Closure

/-
  Layer 2: 집합론 on 213 Firmware.
  gen → 원소. mul → 소속 판정. Triple → 3-집합.
-/

-- ═══ 집합의 213 구현 ═══

-- 집합 = Obj의 모음. 판정 함수로 표현.
def Set213 := Obj → Bool

-- 공집합: 아무 원소 없음.
def emptySet : Set213 := fun _ => false

-- 전체집합: 모든 Obj 포함.
def fullSet : Set213 := fun _ => true

-- 원소 소속: mul로 판정.
-- a ∈ S ↔ S a = true.
def mem (S : Set213) (a : Obj) : Bool := S a

-- ═══ 집합 연산 = 213 연산 ═══

-- 합집합: a ∈ A∪B ↔ a ∈ A ∨ a ∈ B.
def union (A B : Set213) : Set213 := fun x => A x || B x

-- 교집합: a ∈ A∩B ↔ a ∈ A ∧ a ∈ B.
def inter (A B : Set213) : Set213 := fun x => A x && B x

-- 여집합: a ∈ Aᶜ ↔ a ∉ A. ← ¬ 사용!
def compl (A : Set213) : Set213 := fun x => !A x

-- ═══ 213 API 대응 ═══

-- gen i → 원소. "이 원소가 있다."
-- mul a b → 비교. "a와 b가 같은 집합에 있는가?"
-- ¬ (compl) → 여집합. 213의 ¬ = 비생성.

-- ═══ 유한 집합: Triple로 ═══

-- 3-원소 집합 = Triple의 원소들로 구성.
def tripleSet (t : Triple Obj) : Set213 := fun x =>
  decide (x = t.x) || decide (x = t.y) || decide (x = t.z)

-- ═══ 핵심: compl은 비생성 ═══

-- union, inter: 기존 집합에서 새 원소 안 만듦.
-- compl: "아닌 것"의 집합. 새 원소를 나열하지 않음.
-- 213 Firmware: gen + mul만 원소 생성.
-- compl(A)의 원소를 나열하려면 전체집합을 알아야 함.
-- 전체집합 = 모든 Obj = 무한.
-- → compl은 유한 절차로 열거 불가. (¬ 비생성의 집합론 버전.)

-- ═══ Layer 2 API ═══

-- 상위 계층(OS: 정리)이 사용할 수 있는 것:
-- emptySet, fullSet, mem, union, inter, compl, tripleSet.
-- Firmware의 gen/mul을 직접 안 씀. 이 API로 추상화.
