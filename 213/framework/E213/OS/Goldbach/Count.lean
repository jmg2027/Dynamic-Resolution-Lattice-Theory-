import E213.OS.Goldbach.Statement

/-
  골드바흐 표현 수 G(n)의 성장.
  G(n) = #{(p,q) : p+q=n, p≤q, p,q prime}.
  G(n) > 0 이 Goldbach. G(n) → ∞ 이 HL 추측.
-/

-- ═══ 표현 수 계산 ═══

def goldbachCount (n : Nat) : Nat :=
  ((List.range (n/2 + 1)).filter fun p =>
    isPrime p && isPrime (n - p)).length

-- 구체적 값:
#eval goldbachCount 4    -- 1: (2,2)
#eval goldbachCount 10   -- 2: (3,7), (5,5)
#eval goldbachCount 20   -- 2: (3,17), (7,13)
#eval goldbachCount 30   -- 3: (7,23), (11,19), (13,17)
#eval goldbachCount 50   -- 4
#eval goldbachCount 100  -- 6

-- ═══ G(n) > 0 검증 ═══

def noZero (bound : Nat) : Bool :=
  (List.range bound).all fun k =>
    goldbachCount (2*k + 4) > 0

theorem positive_to_200 : noZero 100 = true := by native_decide
theorem positive_to_500 : noZero 250 = true := by native_decide

-- ═══ 최소 표현 수 ═══

def minGC (bound : Nat) : Nat :=
  (List.range bound).foldl (fun m k =>
    Nat.min m (goldbachCount (2*k + 4))) 9999

#eval minGC 50   -- 100까지 최소
#eval minGC 250  -- 500까지 최소

-- 최소가 1 이상: G(n) ≥ 1 for all even n ≤ 500.
theorem min_positive : minGC 250 ≥ 1 := by native_decide

-- ═══ 성장 확인 ═══

-- G(n)의 10단위 평균:
def avgGC (start count : Nat) : Nat :=
  let total := (List.range count).foldl (fun s k =>
    s + goldbachCount (start + 2*k)) 0
  total / count

#eval avgGC 10 25    -- n=10~60 평균
#eval avgGC 100 25   -- n=100~150 평균
#eval avgGC 200 25   -- n=200~250 평균
#eval avgGC 400 25   -- n=400~450 평균

-- 평균이 증가: 표현 수가 성장.
-- 이것이 Hardy-Littlewood: G(n) ~ C·n/ln²(n) → ∞.

-- ═══ HL 예측과 비교 ═══

-- ln 근사: log₂(n) × 693 / 1000.
def lnApprox (n : Nat) : Nat :=
  if n ≤ 2 then 1
  else Nat.max 1 (Nat.log 2 n * 693 / 1000)

-- HL 예측 (C₂≈1.32 → 132/100):
def hlPred (n : Nat) : Nat :=
  let l := lnApprox n
  if l == 0 then 0 else 132 * n / (100 * l * l)

-- 실제 vs 예측:
#eval (List.range 10).map fun k =>
  let n := 50 * (k + 1)
  (n, goldbachCount n, hlPred n)

-- G(n)>0: depth 1(개별). G(n)→∞: depth ω(∀). gap = C(2,2)=1.
