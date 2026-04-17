/-
  E213/Verify.lean — 모든 주장을 2(판정)한다

  주석으로 적었던 것들을 전부 equivDecide 또는 #eval로 확인.
  말이 아니라 결과.
-/
import E213.Normalize

open Expr

-- ═══ 213.md의 주장들 ═══

-- "2+3 = 213 (def +에 의해 문자 그대로)"
#eval equivDecide (plus e₂ e₃) (plus e₂ e₃)  -- true (자기 자신)
-- 213 = [2,1,3] 문자열로서의 동치는 Expr 수준이 아니라 표기 수준.
-- Expr 수준에서: plus e₂ e₃는 하나의 표현식. 판정 대상 아님.

-- "0 = 11"
#eval equivDecide (plus e₁ e₁) e₁  -- true. 11 ≈ 1.

-- ═══ 교환법칙 ═══
#eval equivDecide (plus e₂ e₃) (plus e₃ e₂)           -- true
#eval equivDecide (times e₂ e₃) (times e₃ e₂)         -- true

-- ═══ 결합법칙 ═══
#eval equivDecide
  (plus (plus e₂ e₃) e₂)
  (plus e₂ (plus e₃ e₂))                              -- true
#eval equivDecide
  (times (times e₂ e₃) e₂)
  (times e₂ (times e₃ e₂))                            -- true

-- ═══ 경계 흡수 (plus_e1) ═══
#eval equivDecide (plus e₁ e₂) e₂                     -- true
#eval equivDecide (plus e₁ e₃) e₃                     -- true
#eval equivDecide (plus e₂ e₁) e₂                     -- true

-- ═══ 경계 소멸 (times_e1) ═══
#eval equivDecide (times e₁ e₂) e₁                    -- true
#eval equivDecide (times e₁ e₃) e₁                    -- true
#eval equivDecide (times e₂ e₁) e₁                    -- true

-- ═══ 분배 ═══
#eval equivDecide
  (times e₂ (plus e₃ e₂))
  (plus (times e₂ e₃) (times e₂ e₂))                 -- true
#eval equivDecide
  (times e₃ (plus e₂ e₃))
  (plus (times e₃ e₂) (times e₃ e₃))                 -- true

-- ═══ 우분배 (따름정리) ═══
#eval equivDecide
  (times (plus e₂ e₃) e₂)
  (plus (times e₂ e₂) (times e₃ e₂))                 -- true

-- ═══ 소멸-분배 정합성 ═══
-- 직접: 1×(2+3) ≈ 1
#eval equivDecide (times e₁ (plus e₂ e₃)) e₁          -- true
-- 분배 후: 1×2 + 1×3 ≈ 1+1 ≈ 1
#eval equivDecide
  (plus (times e₁ e₂) (times e₁ e₃)) e₁              -- true
-- 두 경로 같은 결과
#eval equivDecide
  (times e₁ (plus e₂ e₃))
  (plus (times e₁ e₂) (times e₁ e₃))                 -- true

-- ═══ swap 불변 (대칭 다항식) ═══
-- σ₁ = e₂ + e₃. swap(σ₁) = e₃ + e₂ ≈ σ₁.
#eval equivDecide (plus e₂ e₃) (plus e₃ e₂)           -- true
-- σ₂ = e₂ × e₃. swap(σ₂) = e₃ × e₂ ≈ σ₂.
#eval equivDecide (times e₂ e₃) (times e₃ e₂)         -- true
-- e₂²+e₃² ≈ e₃²+e₂² (swap 불변)
#eval equivDecide
  (plus (times e₂ e₂) (times e₃ e₃))
  (plus (times e₃ e₃) (times e₂ e₂))                 -- true

-- ═══ 비동치 ═══
#eval equivDecide e₂ e₃                               -- false
#eval equivDecide e₁ e₂                               -- false
#eval equivDecide (plus e₂ e₃) (times e₂ e₃)          -- false
#eval equivDecide (times e₂ e₂) (times e₃ e₃)         -- false

-- ═══ eval 수치 (관찰용) ═══
#eval exprEval e₁ 2 3             -- 0
#eval exprEval e₂ 2 3             -- 2
#eval exprEval e₃ 2 3             -- 3
#eval exprEval (plus e₂ e₃) 2 3   -- 5 = d
#eval exprEval (times e₂ e₃) 2 3  -- 6 = σ₂
#eval exprEval
  (times (plus e₂ e₃) (plus e₂ e₃)) 2 3  -- 25 = d²

-- ═══ C(3,2) = 3 ═══
#eval (3 * 2 / 2 : Nat)           -- 3 = C(3,2)
#eval (3 * 2 / 2 == 3 : Bool)     -- true (고정점)
#eval (2 * 1 / 2 == 2 : Bool)     -- false (C(2,2)=1≠2)
#eval (4 * 3 / 2 == 4 : Bool)     -- false (C(4,2)=6≠4)

-- ═══ Cayley-Dickson ═══
-- 가산원자 ∩ {1,2,4,8} = {2}
#eval ([1,2,4,8].filter fun d =>
  d >= 2 && !(List.range (d-1) |>.drop 2 |>.any
    fun a => d - a >= 2))          -- [2]

-- ═══ 전부 판정됨. 말 아님. ═══
