import E213.Lib.Math.NumberSystems.Padic.Foundation
import E213.Lib.Math.NumberSystems.Padic.Arith
import E213.Lib.Math.NumberSystems.Padic.Norm
/-!
# Real213-p-adic — canonical 5-adic embeddings

The 5-adic Real213 provides a canonical embedding `ℕ ↪ ZpSeq 5` for
any natural number via `digits_of_nat`.  This file records a few
canonical instances and their digit smoke-tests.

Whether the "infinite" 5-adic structure is operationally meaningful
in DRLT, or is a formal extension only, is itself a research
question.
-/

namespace E213.Lib.Math.NumberSystems.Padic

/-- The all-zero 5-adic. -/
def canonical_5adic_zero : ZpSeq 5 :=
  ZpSeq.zero 5 (by decide)

/-! ## Canonical 5-adic lift of the base prime -/

/-- The 5-adic lift of `5` itself — has digit 1 at position 1
    and zero elsewhere. -/
def canonical_5adic_p : ZpSeq 5 :=
  ZpSeq.digits_of_nat 5 (by decide) 5

/-- Digit-0 of `5` in base 5 is `0`. -/
theorem canonical_5adic_p_digit_0 :
    (canonical_5adic_p.digits 0).val = 0 := by decide

/-- Digit-1 of `5` in base 5 is `1`. -/
theorem canonical_5adic_p_digit_1 :
    (canonical_5adic_p.digits 1).val = 1 := by decide

/-- Digit-2 of `5` in base 5 is `0`. -/
theorem canonical_5adic_p_digit_2 :
    (canonical_5adic_p.digits 2).val = 0 := by decide

end E213.Lib.Math.NumberSystems.Padic
