import E213.Axiom

/-
  접속 행렬로 구분의 구조적 증명.
  행이 같으면 구분 불가. 다르면 구분 가능.
  n=2: 행 동일. n=3: 행 전부 다름. 메타도 동형.
-/

-- 접속 행렬: 객체 i가 관계 j에 참여하는가.
-- 관계 (a,b)에 i 참여 ↔ i=a 또는 i=b.

-- ═══ n=2 ═══
-- 관계 1개: (0,1). 둘 다 참여.
def inc2 (_i : Fin 2) : List Bool := [true]

theorem same_2 : inc2 0 = inc2 1 := by native_decide

-- ═══ n=3 ═══
-- 관계 3개: (0,1), (0,2), (1,2).
def inc3 (i : Fin 3) : List Bool :=
  match i.val with
  | 0 => [true, true, false]
  | 1 => [true, false, true]
  | _ => [false, true, true]

theorem diff_01 : inc3 0 ≠ inc3 1 := by native_decide
theorem diff_02 : inc3 0 ≠ inc3 2 := by native_decide
theorem diff_12 : inc3 1 ≠ inc3 2 := by native_decide

-- ═══ 왜 다른가 ═══
-- 각 행에 false가 정확히 하나. 위치가 다름.
-- false = 나를 포함하지 않는 관계 = 나머지 둘의 관계.
-- 이것이 증인: 제3자의 존재가 나를 식별.
-- n=2: false 없음. 증인 없음. 구분 불가.
-- n=3: false 정확히 하나. 증인 정확히 하나.

-- ═══ 메타레벨: 관계를 객체로 ═══
-- 관계 3개. 두 관계가 "관련" = 공유 객체 있음.
-- 모든 쌍이 공유 → 메타도 K₃ → 접속 행렬 동형.

-- 메타 행렬 = inc3과 같은 구조.
-- 관계(0,1)의 행: [참,참,불참] (= inc3 0).
-- 관계(0,2)의 행: [참,불참,참] (= inc3 1).
-- 관계(1,2)의 행: [불참,참,참] (= inc3 2).
-- 기본 행렬과 동형!

-- ═══ 정사각 ↔ 동형 보존 ═══
-- 행렬 크기: n × C(n,2). 정사각 ↔ n = C(n,2) ↔ n = 3.
-- 정사각일 때만 메타레벨이 원래와 동형.
theorem square_only_3 :
    (List.range 100).filter (fun n => n > 0 && n == pairs n)
    = [3] := by native_decide

-- ═══ 요약 ═══
structure DistinctionProof where
  fail : inc2 0 = inc2 1
  d01 : inc3 0 ≠ inc3 1
  d02 : inc3 0 ≠ inc3 2
  d12 : inc3 1 ≠ inc3 2
  unique : (List.range 100).filter
    (fun n => n > 0 && n == pairs n) = [3]

theorem distinction : DistinctionProof where
  fail := by native_decide
  d01 := by native_decide
  d02 := by native_decide
  d12 := by native_decide
  unique := by native_decide
