import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
/-!
# Real213-p-adic — DRLT integration

The DRLT resolution lattice uses `N_U = 5^25` as its count-Lens
universe size at fractal level 2.  The 5-adic Real213 picks up
exactly where the finite-resolution lattice stops, providing a
canonical embedding `ℕ ↪ ZpSeq 5` for any natural number.

The lift `N_U → ZpSeq 5` is `digits_of_nat 5 N_U`, which has
digit 25 equal to `1` and all other digits equal to `0` (since
`5^25 = 1 · 5^25 + 0 · …`).

Whether the "infinite" 5-adic structure beyond the resolution
limit is operationally meaningful in DRLT, or is a formal
extension only, is itself a research question — see
`seed/RESOLUTION_LIMIT_SPEC.md`.
-/

namespace E213.Lib.Math.Padic

/-- The canonical 5-adic lift of `N_U = 5^25`. -/
def canonical_5adic_NU : ZpSeq 5 :=
  ZpSeq.digits_of_nat 5 (by decide) (5^25)

/-- The all-zero 5-adic. -/
def canonical_5adic_zero : ZpSeq 5 :=
  ZpSeq.zero 5 (by decide)

/-- Smoke: digit-0 of `5^25` in base 5 is `0` (since `5^25` is
    divisible by `5`). -/
theorem canonical_5adic_NU_digit_0 :
    (canonical_5adic_NU.digits 0).val = 0 := rfl

/-- Smoke: digit-1 of `5^25` in base 5 is `0`. -/
theorem canonical_5adic_NU_digit_1 :
    (canonical_5adic_NU.digits 1).val = 0 := rfl

end E213.Lib.Math.Padic
