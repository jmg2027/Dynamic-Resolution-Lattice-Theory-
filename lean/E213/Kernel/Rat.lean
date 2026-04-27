import E213.Kernel.Term
import E213.Kernel.Compare

/-!
# E213.Kernel.Rat — 213 의 rational arithmetic (cross-multiplication).

CLAUDE.md: "유한 이산 격자 — ÷ (division) → ℚ 산술의 부산물".
ℚ 자체를 별도 type 으로 안 만듦.  분자/분모를 두 Term 으로 들고,
*cross-multiplication* 으로 등호 검사 → ℕ 안에 머무름.

  p/q ≡ r/s  ⇔  p·s = q·r

→ Lean Rat 도, quotient 도 안 씀.  0 axiom 유지.
-/

namespace E213.Kernel.Term

/-- Rational equivalence via cross-multiplication (Bool). -/
def equivQ (p q r s : Term) : Bool :=
  equiv (mul p s) (mul q r)

/-- Rational ≤ via cross-multiplication: p/q ≤ r/s ⇔ p·s ≤ q·r
    (q, s 양수 가정 — 213 에선 분모 0 안 씀). -/
def leQ (p q r s : Term) : Bool :=
  le_b (mul p s) (mul q r)

end E213.Kernel.Term

namespace E213.Kernel.Rat

open Term

-- 213 정수 (ℕ 인코딩 helper)
def n6  : Term := mul nS (succ (succ zero))     -- 3·2 = 6
def n10 : Term := mul d (succ (succ zero))      -- 5·2 = 10
def n25 : Term := mul d d                        -- 25

/-- 6/10 ≡ 3/5  (K_{3,2} bipartite probability 약분). -/
theorem six_ten_eq_three_five :
    equivQ n6 n10 nS d = true := rfl

/-- 1/2 ≡ 5/10. -/
theorem half_eq_five_ten :
    equivQ (succ zero) (succ (succ zero)) d n10 = true := rfl

/-- α_GUT 분자/분모 토대: 6/25  (π² 무시한 lower bound).
    실제 α_GUT = 6/(25·π²) ≈ 0.024. -/
theorem alphaGUT_base : equivQ n6 n25 n6 n25 = true := rfl

/-- d²/4 = 25/4  (uneven, 약분 안 됨). -/
theorem dsq_over_four_irred :
    equivQ (mul d d) (mul (succ (succ zero)) (succ (succ zero)))
           n25 (mul (succ (succ zero)) (succ (succ zero))) = true := rfl

/-- 6/25 < 1/4  (α_GUT 가 1/4 보다 작음 — 약결합). -/
theorem alphaGUT_lt_quarter :
    leQ n6 n25 (succ zero) (mul (succ (succ zero)) (succ (succ zero)))
    = true := rfl

end E213.Kernel.Rat

#print axioms E213.Kernel.Rat.six_ten_eq_three_five
#print axioms E213.Kernel.Rat.half_eq_five_ten
#print axioms E213.Kernel.Rat.alphaGUT_base
#print axioms E213.Kernel.Rat.dsq_over_four_irred
#print axioms E213.Kernel.Rat.alphaGUT_lt_quarter
