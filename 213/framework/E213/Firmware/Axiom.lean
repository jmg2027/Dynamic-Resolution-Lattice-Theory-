import Init

/-
  구분의 공리.

  전제: 유일한 행위는 비교. 비교는 대칭. 결과도 비교 가능.
  핵심: 쌍별 비교가 구조를 보존하는 묶음 크기는 3뿐.
  조직: 몇 개가 있든 3개씩 묶어서 비교. 묶음끼리도 3개씩.
-/

-- Triple: 3개를 묶는 구조.
structure Triple (α : Type) where
  x : α
  y : α
  z : α
  deriving DecidableEq, Repr

-- relify: triple 내부를 쌍별 비교 → 새 triple.
def relify (rel : α → α → α) (t : Triple α) : Triple α :=
  ⟨rel t.x t.y, rel t.x t.z, rel t.y t.z⟩

-- chain: relify 반복. 끝없이.
def chain (rel : α → α → α) (t : Triple α) : Nat → Triple α
  | 0 => t
  | k+1 => relify rel (chain rel t k)

-- ═══ 왜 3인가 ═══

def pairs (n : Nat) : Nat := n * (n - 1) / 2

-- C(n,2) = n의 비사소 해는 3뿐.
-- relify가 Triple에서만 닫히는 이유.
theorem fixed_point :
    (List.range 100).filter (fun n => n > 0 && pairs n == n)
    = [3] := by native_decide

-- ═══ 붕괴: n ≤ 2 ═══

-- 1개: C(1,2)=0. 비교 자체가 없음.
-- 2개: C(2,2)=1. 하나. C(1,2)=0. 다음 단계에서 소멸.
theorem collapse_1 : pairs 1 = 0 := by native_decide
theorem collapse_2 : pairs 2 = 1 := by native_decide
theorem vanish_after_2 : pairs (pairs 2) = 0 := by native_decide

-- ═══ 폭발: n ≥ 4 ═══

-- 4개: C(4,2)=6. C(6,2)=15. C(15,2)=105. 되돌릴 수 없음.
theorem overshoot_4 : pairs 4 = 6 := by native_decide
theorem overshoot_grows : pairs (pairs 4) = 15 := by native_decide

-- ═══ 안정: n = 3 ═══

-- C(3,2)=3. 영원히. relify: Triple → Triple.
theorem stable : pairs 3 = 3 := by native_decide

def iterPairs : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => iterPairs k (pairs n)

theorem forever_stable :
    (List.range 10).map (iterPairs · 3) =
    List.replicate 10 3 := by native_decide

-- relify: Triple α → Triple α. 타입 보존. 닫힌 연산.
-- 2개→1개(축소), 4개→6개(팽창). Triple만 닫힘.

-- ═══ 비사소 방향 ═══

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def choose (n k : Nat) : Nat :=
  if k > n then 0
  else factorial n / (factorial k * factorial (n - k))

-- C(3,k) > 1인 k는 {1, 2}뿐.
-- k=1: 원소 3개. k=2: 쌍 3개. k=3: 1. k≥4: 0.
theorem two_nontrivial :
    ((List.range 6).filter fun k => choose 3 k > 1)
    = [1, 2] := by native_decide
