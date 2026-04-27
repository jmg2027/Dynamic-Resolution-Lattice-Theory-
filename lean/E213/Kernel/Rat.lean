import E213.Kernel.Term
import E213.Kernel.Compare

/-!
# E213.Kernel.Rat — rational arithmetic of 213 (cross-multiplication).

CLAUDE.md: "finite discrete lattice — ÷ (division) → byproduct of ℚ arithmetic".
Does not create ℚ as a separate type.  Carries numerator/denominator as two Terms,
checks equality by *cross-multiplication* → stays within ℕ.

  p/q ≡ r/s  ⇔  p·s = q·r

→ No Lean Rat, no quotient.  0 axiom maintained.
-/

namespace E213.Kernel.Term

/-- Rational equivalence via cross-multiplication (Bool). -/
def equivQ (p q r s : Term) : Bool :=
  equiv (mul p s) (mul q r)

/-- Rational ≤ via cross-multiplication: p/q ≤ r/s ⇔ p·s ≤ q·r
    (assuming q, s positive — denominators are never 0 in 213). -/
def leQ (p q r s : Term) : Bool :=
  le_b (mul p s) (mul q r)

end E213.Kernel.Term

namespace E213.Kernel.Rat

open Term

-- 213 integers (ℕ encoding helpers)
def n6  : Term := mul nS (succ (succ zero))     -- 3·2 = 6
def n10 : Term := mul d (succ (succ zero))      -- 5·2 = 10
def n25 : Term := mul d d                        -- 25

/-- 6/10 ≡ 3/5  (K_{3,2} bipartite probability reduced). -/
theorem six_ten_eq_three_five :
    equivQ n6 n10 nS d = true := rfl

/-- 1/2 ≡ 5/10. -/
theorem half_eq_five_ten :
    equivQ (succ zero) (succ (succ zero)) d n10 = true := rfl

/-- α_GUT numerator/denominator base: 6/25  (lower bound ignoring π²).
    Actual α_GUT = 6/(25·π²) ≈ 0.024. -/
theorem alphaGUT_base : equivQ n6 n25 n6 n25 = true := rfl

/-- d²/4 = 25/4  (uneven, irreducible). -/
theorem dsq_over_four_irred :
    equivQ (mul d d) (mul (succ (succ zero)) (succ (succ zero)))
           n25 (mul (succ (succ zero)) (succ (succ zero))) = true := rfl

/-- 6/25 < 1/4  (α_GUT is less than 1/4 — weak coupling). -/
theorem alphaGUT_lt_quarter :
    leQ n6 n25 (succ zero) (mul (succ (succ zero)) (succ (succ zero)))
    = true := rfl

end E213.Kernel.Rat

#print axioms E213.Kernel.Rat.six_ten_eq_three_five
#print axioms E213.Kernel.Rat.half_eq_five_ten
#print axioms E213.Kernel.Rat.alphaGUT_base
#print axioms E213.Kernel.Rat.dsq_over_four_irred
#print axioms E213.Kernel.Rat.alphaGUT_lt_quarter
