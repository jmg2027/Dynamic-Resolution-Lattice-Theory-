import E213.Meta.MetaTower

/-
  Goldbach 의 213 분석.

  명제: ∀ n ≥ 4 짝수, ∃ 소수 p, q 로 n = p + q.

  현실:
    - 1742 년 Euler-Goldbach 제안.
    - 280+ 년 미해결.
    - 계산 검증 4 × 10¹⁸ 까지.
    - ZFC 내 증명 미존재.

  213 접근:
    1. Encode: isPrime + goldbachCheck 를 decidable 로.
    2. 유한 검증 (decide).
    3. Provability category 분석.
    4. Lens requirement.
    5. 정직한 한계 명시.
-/

-- ═══ isPrime: Decidable 소수 판정 ═══

def isPrime (n : Nat) : Bool :=
  decide (n ≥ 2) &&
  (List.range n).all (fun k => decide (k < 2) || decide (n % k ≠ 0))

-- 작은 소수 확인.
example : isPrime 2 = true := by decide
example : isPrime 3 = true := by decide
example : isPrime 4 = false := by decide
example : isPrime 5 = true := by decide
example : isPrime 7 = true := by decide
example : isPrime 9 = false := by decide

-- ═══ Goldbach pair finder ═══

-- n 을 두 소수 합 으로 표현하는 pair (p, q) 탐색.
def goldbachPair (n : Nat) : Option (Nat × Nat) :=
  (List.range n).findSome? (fun p =>
    if isPrime p && isPrime (n - p) then some (p, n - p) else none)

-- Goldbach 조건: 짝수 ≥ 4 이면 pair 존재.
def goldbachCheck (n : Nat) : Bool :=
  if n < 4 then true
  else if n % 2 ≠ 0 then true
  else (goldbachPair n).isSome

-- ═══ 구체 검증 ═══

-- 작은 짝수 들 확인.
example : goldbachCheck 4 = true := by decide    -- 2 + 2
example : goldbachCheck 6 = true := by decide    -- 3 + 3
example : goldbachCheck 8 = true := by decide    -- 3 + 5
example : goldbachCheck 10 = true := by decide   -- 3 + 7
example : goldbachCheck 12 = true := by decide   -- 5 + 7
example : goldbachCheck 100 = true := by decide  -- 3 + 97

-- ═══ 213 Category 분석 ═══

-- Goldbach 의 Problem213 encoding.
-- Raw → Nat via Lens.depth.
-- 그 Nat 에서 goldbachCheck 적용.

def goldbach_problem : Problem213 :=
  { name := "Goldbach conjecture (stated for depth n)"
    prop := fun x => goldbachCheck x.depth = true
    decInst := fun x => inferInstanceAs (Decidable _) }

-- Level 0 까지 확인 (Raw 원소 3개).
-- depth 0 모두 → 0 < 4 → trivially true.
example : goldbach_problem.conjectureProvable 0 = true := by
  native_decide

-- ═══ Category 분류 ═══

-- Goldbach 의 213 profile:
-- Category: kernelFail (ZFC 에서 미해결, Category 1 후보).
-- Verdict: unknown (open problem).
-- Requirement:
--   Rules R1-R6: 전부 활성.
--   Stream: 아니 (discrete Nat).
--   Uncountable: 아니.
-- Difficulty: 6 (Rule) + 0 + 0 = 6.
--   하지만 "실제" 난이도 는 훨씬 큼 (미해결).

def goldbach_profile : ProblemProfile :=
  { problem := ⟨"Goldbach", fun _ => True, Lens.depth⟩
    verdict := .unknown
    category := .kernelFail
    requirement :=
      { needsR1 := true, needsR2 := true, needsR3 := true
        needsR4 := true, needsR5 := true, needsR6 := true
        needsStream := false, needsUncountable := false }
    difficulty := 6 }

-- ═══ 213 의 답 (정직) ═══

-- Goldbach 완전 증명:
--   ✗ 불가능 (수학계 전체 280 년 미해결).
--
-- 213 이 제공:
--   (1) Encoding: isPrime + goldbachCheck = decidable.
--   (2) 유한 검증: 작은 n decide.
--   (3) Category 분석: kernelFail (ZFC 렌즈 부족).
--   (4) Difficulty: framework 상 6.
--   (5) Heuristic: 검증된 범위 확대 가능.
--
-- 한계:
--   ∀ n 무한 quantifier → 유한 Lean decide 불가.
--   실제 증명 = 수학사 난제.
--
-- 213 의 결론:
--   Goldbach = Category 1 (kernel fail) 후보.
--   ZFC 에서 independent 가능성.
--   더 큰 렌즈 (large cardinal 등) 필요할 수 있음.

-- ═══ 진짜 무한 명제 (사용자 요청) ═══

-- Goldbach 자체: ∀ n 의 statement.
def Goldbach : Prop :=
  ∀ n : Nat, 4 ≤ n → n % 2 = 0 →
    ∃ p q : Nat, isPrime p = true ∧ isPrime q = true ∧ p + q = n

-- ═══ Lens 분석 (진짜) ═══

-- Lens.depth: Raw → Nat. 모든 Nat 값 도달 (depth_image_surjective).
-- 하지만 Lens.depth 는 Nat 의 "구조" (소수성, 짝수성) 를 못 봄.
-- → "소수를 보는 렌즈" 필요.

-- PrimalityLens 후보:
def primBool : Nat → Bool := isPrime

-- 이 함수가 렌즈? Not directly (Raw → α 필요, Nat → Bool 은 Nat 위).
-- 213 에서는 Raw → Nat (depth) → isPrime → Bool 합성.

-- 합성 lens:
def Lens.primality : Lens Bool :=
  ⟨fun i => isPrime i.val,
   fun a b => a && b⟩  -- 두 자식 모두 소수 인가.

-- ═══ Goldbach 의 Category 분석 ═══

-- Goldbach 가 Category 1 (kernel fail) 인가?

-- 두 Raw x, y 가 같은 depth n 이면:
-- 둘 다 같은 Nat 으로 간주.
-- Goldbach(n) = Goldbach(n). 동일.
-- → depth 렌즈 는 Goldbach 를 trivially respect.
-- → Category 1 **아님** (depth 수준에서).

-- 하지만 "Raw → Nat → Goldbach" 의 Raw → Nat 부분은
-- 기본 213 렌즈. 문제는 Nat 수준의 Goldbach.
-- Nat 위 Goldbach 는 213 framework 밖 의 arithmetic.

-- ═══ 진짜 결론 ═══

-- Goldbach 의 "∀ n" 은 Nat 위 arithmetic 명제.
-- 213 은 Nat 을 생성 (depth) 하지만 Nat 위 소수론 은 별도.
-- 213 framework 자체 는 Goldbach 증명 도구 제공 X.
--
-- 즉 Goldbach 는:
--   (1) 213 내 encoding 가능 (isPrime Bool).
--   (2) 213 범위 밖 의 Nat arithmetic 이 증명 지배.
--   (3) 213 의 렌즈 부족 이 문제 가 아님 (렌즈는 충분).
--   (4) **Arithmetic theory 자체 의 한계**.

-- 사용자 질문 의 정확한 답:
--   Goldbach 의 어려움 = 213 렌즈 부족 아님.
--   Arithmetic 의 한계 (PA 또는 ZFC 의 소수 분포 표현력).
--   Category 1 후보 이지만 "렌즈 섬세화" 로 해결 못 함.
--   해결 = 새 arithmetic 정리 (수학사 난제).

-- 213 framework 의 진단:
--   "렌즈는 충분. 하지만 그 렌즈 위 의 Nat 구조 가 Goldbach 를
--    자동 증명 하지 못함. 이건 Nat 구조 의 특성 (소수 불규칙성)."
