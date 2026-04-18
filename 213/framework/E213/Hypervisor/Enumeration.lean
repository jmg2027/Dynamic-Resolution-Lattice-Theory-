import E213.Hypervisor.Numbers

/-
  수 = Reachable 객체의 열거 순서.

  모든 Reachable은 유일 (diff_inputs_diff_output).
  → 순서대로 번호 매기면 Nat과 1:1 대응.
  → 이것이 "수"의 가장 단순한 정의.

  핵심:
    1. 번호 매기기는 선택 (왼쪽/오른쪽/깊이 우선...).
    2. 같은 index가 순서에 따라 다른 객체를 가리킴.
    3. 하지만 image 집합은 같음 (Reachable 전체).
    4. depth/leaves/nodes는 순서 무관 (객체의 성질).
    → 번호는 라벨. 구조가 본질.
-/

-- ═══ 두 열거: A(왼쪽 우선), B(오른쪽 우선) ═══

-- 순서 A: 생성 시점 그대로.
def enumA : List Raw := [a₀, b₀, ab₀, aab₀, bab₀]

-- 순서 B: 3,4번 자리만 교체.
def enumB : List Raw := [a₀, b₀, ab₀, bab₀, aab₀]

-- ═══ 같은 index, 다른 객체 (순서 의존) ═══

example : enumA[3]? = some aab₀ := by decide
example : enumB[3]? = some bab₀ := by decide
example : enumA[3]? ≠ enumB[3]? := by decide

-- ═══ 같은 image 집합 (순서 무관) ═══

-- 원소 집합은 같음. 순서만 다름.
example : enumA.dedup.length = enumB.dedup.length := by decide

-- 더 강하게: 각 원소는 양쪽에 모두 있음.
example : aab₀ ∈ enumA := by decide
example : aab₀ ∈ enumB := by decide
example : bab₀ ∈ enumA := by decide
example : bab₀ ∈ enumB := by decide

-- ═══ 구조적 수는 순서 무관 ═══

-- 객체의 depth/leaves/nodes는 "몇 번째"와 무관.
-- aab₀가 index 3이든 4이든 depth는 항상 2.
example : aab₀.depth  = 2 := by decide
example : aab₀.leaves = 3 := by decide
example : aab₀.nodes  = 5 := by decide

-- bab₀도 마찬가지.
example : bab₀.depth  = 2 := by decide
example : bab₀.leaves = 3 := by decide

-- ═══ Injective 열거 (1:1 대응) ═══

-- enumA는 중복 없음 (모든 Reachable 객체가 유일하므로).
example : enumA.Nodup := by decide
example : enumB.Nodup := by decide

-- 따라서 index가 같으면 객체도 같음 (한 리스트 안에서).
example : ∀ i j, i < enumA.length → j < enumA.length →
    enumA[i]? = enumA[j]? → i = j := by decide

-- ═══ 일반 정리: 번호 매기기는 선택 ═══

-- 같은 Reachable 집합의 두 Nodup 열거는 치환(permutation) 관계.
-- List.Perm이 이것을 표현. 순서만 다름.

-- enumA와 enumB가 치환.
example : List.Perm enumA enumB := by decide

-- List.Perm의 성질: 길이, 원소 집합, 카운트 모두 보존.
-- 차이점: index ↔ 객체 대응만 다름.

-- ═══ 결론 (공식화) ═══

-- 1. Reachable 집합은 고정 (객체의 실제 존재).
-- 2. 열거 순서는 선택 (List.Perm까지만 규정됨).
-- 3. 구조적 수 (depth/leaves/nodes)는 객체의 성질 → 순서 무관.
-- 4. 열거 index는 선택에 의존 → 라벨.

-- 따라서:
--   "수"의 두 개념:
--     (a) 열거 번호 — 선택 (라벨).
--     (b) 구조 성질 — 본질 (/에서 내장된 것).
--   (a)는 (b)를 결정하지 못하고, (b)는 (a)에 무관.
--   번호가 본질이 아니라 구조가 본질.

-- 이것이 "번호는 임의의 라벨"의 형식 증거.
