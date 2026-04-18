import E213.Firmware.Axiom
import E213.Translation.Decompose
import E213.OS.Goldbach.Statement

/-
  골드바흐 추측의 213 원소 분해.
  추측의 각 부분이 gen/mul/= 몇 개로 구성되는가.
-/

-- ═══ "짝수" 의 비용 ═══
-- n % 2 == 0. =_1 비교 1번.
def costEven : Cost := ⟨1, 0, 1⟩  -- gen 1(n), mul 0, depth 1(=_1)

-- ═══ "소수" 의 비용 (고정 n) ═══
-- n-2번의 나눗셈 검사. 각 검사 = mul 1 + =_0 1.
-- gen 1(n) + mul (n-2)(나눗셈) + depth 1.
def costPrime (n : Nat) : Cost := ⟨1, n - 2, 1⟩

#eval costPrime 7    -- (1, 5, 1): 5번 나눗셈 검사
#eval costPrime 101  -- (1, 99, 1): 99번 검사

-- ═══ "p + q = n" 의 비용 ═══
-- gen 2(p, q 선택) + mul 1(덧셈 확인) + depth 1(=).
def costSum : Cost := ⟨2, 1, 1⟩

-- ═══ "∃ p q" 의 비용 ═══
-- 최악 n/2번 시도. 각 시도 = costPrime × 2 + costSum.
def costExists (n : Nat) : Cost :=
  ⟨n, n * (n - 2), 1⟩  -- 대략적 상한

-- ═══ 개별 goldbach(n)의 총 비용 ═══
-- depth 1. gen O(n). mul O(n²). 유한!
#eval costExists 100   -- (100, 9800, 1)
#eval costExists 1000  -- (1000, 998000, 1)

-- ═══ "∀ even n > 2" 의 비용 ═══
-- gen ∞. mul ∞. depth ω!
-- 이것이 유한에서 무한으로의 전이.
def costForAll : Cost := ⟨100, 100, 100⟩  -- 100 = ω 근사

-- ═══ 추측 전체의 213 분해 ═══

-- 골드바흐 = costForAll ∘ costExists ∘ (costPrime × 2 + costSum)
-- = ∀(∃(소수 × 소수 + 합))
-- depth: max(ω, 1, 1, 1) = ω.
-- ∀이 전체 depth를 지배.

-- 개별(n 고정): ⟨~n, ~n², 1⟩. 유한. 검증 가능. full.
-- 전체(∀n): ⟨∞, ∞, ω⟩. 무한. 추측. partial.

theorem individual_is_finite :
    (costPrime 100).d = 1 := rfl

theorem forall_dominates :
    costForAll.d > (costPrime 100).d := by native_decide
