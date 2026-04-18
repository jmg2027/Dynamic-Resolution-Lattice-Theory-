import E213.Firmware.Axiom

/-
  ε-δ 연속성의 213 번역.
  ε = 출력 해상도 (chain level). δ = 입력 해상도.
  =_k: mod (k+1)로 같다. 연속: ∀ε ∃δ, =_δ → =_ε.
-/

-- =_k: 해상도 k에서 같다. k↑ → 더 세밀.
def eqAt (k a b : Nat) : Bool := a % (k+1) == b % (k+1)

#eval eqAt 0 3 7  -- true  (mod 1: 전부 같다)
#eval eqAt 1 3 7  -- true  (mod 2: 둘 다 홀수)
#eval eqAt 1 3 8  -- false (mod 2: 홀짝 다름)
#eval eqAt 9 3 7  -- false (mod 10: 3≠7)

-- ═══ ε-δ 연속 ═══

-- f가 (ε,δ)-연속: =_δ 이면 =_ε.
def contAt (f : Nat → Nat) (ε δ n : Nat) : Bool :=
  (List.range n).all fun a =>
    (List.range n).all fun b =>
      !eqAt δ a b || eqAt ε (f a) (f b)

-- ═══ 선형: δ=ε면 연속 ═══

-- f(x)=2x. a≡b(mod m) → 2a≡2b(mod m). 선형.
theorem linear3 : contAt (· * 2) 3 3 20 = true := by native_decide
theorem linear7 : contAt (· * 2) 7 7 30 = true := by native_decide

-- ═══ 제곱: δ > ε 필요할 수 있음 ═══

-- f(x)=x². a²-b²=(a-b)(a+b). a+b 크면 차이 증폭.
#eval contAt (· ^ 2) 3 3 20  -- 확인
#eval contAt (· ^ 2) 3 6 20  -- δ 더 크게

-- ═══ 213 관점 ═══

-- ε → chain level k (출력 해상도)
-- δ → chain level j (입력 해상도)
-- |x-y|<δ → eqAt j x y
-- |f(x)-f(y)|<ε → eqAt k (f x) (f y)
-- 연속 → ∀k ∃j, contAt f k j
-- 균등연속 → j가 x에 무관
-- Lipschitz → j ≤ k + C (차이 유한)

-- depth ω: "∀k" = 모든 chain level = 무한.
-- 유한 chain: "k까지만" 연속 = 근사.

structure ED213 where
  lin3 : contAt (· * 2) 3 3 20 = true
  lin7 : contAt (· * 2) 7 7 30 = true

theorem epsilon_delta : ED213 where
  lin3 := by native_decide
  lin7 := by native_decide
