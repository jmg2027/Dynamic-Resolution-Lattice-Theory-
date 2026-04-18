import E213.Applications.Goldbach

/-
  Arithmetic Zoo: 여러 수론 conjectures 의 213 encoding + partial proofs.

  포함:
    - Twin primes.
    - Collatz.
    - Perfect numbers.
    - Mersenne primes.
    - Fermat small cases.
    - Wilson / Fermat little.

  각각 ArithmeticContent instance.
  유한 case 증명, open 은 명시.
-/

-- ═══ Twin Primes ═══

def twin_prime (n : Nat) : Bool :=
  isPrime n && isPrime (n + 2)

-- 구체 twin primes.
example : twin_prime 3 = true := by decide    -- (3, 5)
example : twin_prime 5 = true := by decide    -- (5, 7)
example : twin_prime 11 = true := by decide   -- (11, 13)
example : twin_prime 17 = true := by decide   -- (17, 19)
example : twin_prime 4 = false := by decide   -- 4 소수 아님

def twin_prime_conjecture : Prop :=
  ∀ N : Nat, ∃ n, N ≤ n ∧ twin_prime n = true

-- ═══ Collatz ═══

def collatz_step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- n 에서 N 스텝 후 1 도달?
def collatz_reaches_one (n N : Nat) : Bool :=
  match N with
  | 0 => n = 1
  | N+1 => n = 1 || collatz_reaches_one (collatz_step n) N

-- 구체 수렴 확인.
example : collatz_reaches_one 1 0 = true := by decide
example : collatz_reaches_one 2 1 = true := by decide   -- 2→1
example : collatz_reaches_one 3 10 = true := by decide  -- 3→10→5→16→8→4→2→1
example : collatz_reaches_one 27 150 = true := by decide -- 긴 경로

def collatz_conjecture : Prop :=
  ∀ n : Nat, n ≥ 1 → ∃ N : Nat, collatz_reaches_one n N = true

-- ═══ Perfect Numbers ═══

def sum_divisors (n : Nat) : Nat :=
  ((List.range n).filter (fun k => k > 0 && n % k = 0)).foldl (· + ·) 0

-- Perfect n = sum_divisors n = n (자기 제외).
def is_perfect (n : Nat) : Bool :=
  sum_divisors n = n

-- 첫 4 perfect: 6, 28, 496, 8128.
example : is_perfect 6 = true := by decide    -- 1+2+3 = 6
example : is_perfect 28 = true := by decide   -- 1+2+4+7+14 = 28
example : is_perfect 12 = false := by decide

-- Euclid-Euler theorem:
-- n 은 even perfect ⟺ n = 2^(p-1) × (2^p - 1) where 2^p - 1 소수.
-- Odd perfect 는 미지.

def odd_perfect_exists : Prop :=
  ∃ n : Nat, n % 2 = 1 ∧ is_perfect n = true

-- ═══ Mersenne Primes ═══

-- M_p = 2^p - 1. p 소수일 때 M_p 가 소수면 Mersenne prime.
def mersenne (p : Nat) : Nat := 2 ^ p - 1

example : mersenne 2 = 3 := by decide    -- M_2 = 3 prime
example : mersenne 3 = 7 := by decide    -- M_3 = 7 prime
example : mersenne 5 = 31 := by decide   -- M_5 = 31 prime
example : mersenne 7 = 127 := by decide  -- M_7 = 127 prime
example : mersenne 11 = 2047 := by decide -- M_11 = 2047 = 23×89, not prime

example : isPrime (mersenne 2) = true := by decide
example : isPrime (mersenne 3) = true := by decide
example : isPrime (mersenne 5) = true := by decide
example : isPrime (mersenne 11) = false := by decide  -- 23 × 89

def mersenne_prime_conjecture : Prop :=
  ∀ N : Nat, ∃ p ≥ N, isPrime p = true ∧ isPrime (mersenne p) = true

-- ═══ Fermat Last Theorem (특정 n) ═══

-- FLT: n ≥ 3 면 x^n + y^n = z^n (x,y,z > 0) 해 없음.
-- n=3 는 Euler 증명. n=일반은 Wiles 1994.

-- 작은 범위 유한 검증.
def flt_has_solution_small (n bound : Nat) : Bool :=
  ((List.range bound).any fun x =>
    (List.range bound).any fun y =>
      (List.range bound).any fun z =>
        x > 0 && y > 0 && z > 0 && x^n + y^n = z^n)

-- Pythagorean (n=2) 는 해 있음.
example : flt_has_solution_small 2 10 = true := by decide  -- 3,4,5

-- n=3 작은 범위 해 없음 (Euler).
example : flt_has_solution_small 3 5 = false := by decide

-- ═══ Fermat Little (Z/pZ) ═══

-- a^p ≡ a (mod p). p=3 은 thm_fermat_little_Z3 (이미 증명).
-- 일반 p 확인 (p=5):
example : ∀ a : Fin 5,
    (a.val^5) % 5 = a.val % 5 := by decide

-- ═══ Twin Prime 유한 사례 ═══

-- 100 이하의 모든 twin prime 찾기.
def twin_primes_below (N : Nat) : List Nat :=
  (List.range N).filter (fun n => twin_prime n)

example : twin_primes_below 20 = [3, 5, 11, 17] := by decide

-- ═══ Collatz Famous Cases ═══

example : collatz_reaches_one 7 20 = true := by decide
example : collatz_reaches_one 27 120 = true := by decide

-- ═══ Framework 적용 요약 ═══

-- 각 conjecture 에 대해 ArithmeticContent instance:
def twin_content : ArithmeticContent :=
  ⟨fun n => twin_prime n = true, inferInstance⟩
def perfect_content : ArithmeticContent :=
  ⟨fun n => is_perfect n = true, inferInstance⟩

-- 모든 것 encoded. 유한 case decided. 무한 는 conjecture.
-- 213 framework: infrastructure 100% 제공.
-- 수학 난제: 증명은 각 arithmetic content 의 고유 문제.

-- 핵심: **framework 로 다 할 수 있는 것 은 encoding + partial.**
-- 핵심 수학 content 는 별도. 하지만 213 이 어떤 content 인지
-- 정확히 진단.
