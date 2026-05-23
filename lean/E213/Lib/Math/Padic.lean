import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Pow
import E213.Lib.Math.Padic.Norm
import E213.Lib.Math.Padic.Hensel
import E213.Lib.Math.Padic.Teichmuller
import E213.Lib.Math.Padic.Field
import E213.Lib.Math.Padic.DRLT
/-!
# Real213-p-adic — umbrella import

The full p-adic number library, 213-native and ∅-axiom.

Sub-modules:
  · `Foundation` — `ZpSeq`, truncation, base-p digit embedding.
  · `Arith` — addition, negation, multiplication with carry FSM;
              ring-quotient theorems `add_trunc` / `mul_trunc`.
  · `Pow` — natural-number power `Zp.pow x n` with trunc compatibility.
  · `Norm` — `valAtLeast` / `valEq` + ultrametric inequalities
              (additive + multiplicative).
  · `Hensel` — Bezout-based digit-0 inverse + Hensel-lifted full
              inverse `invFull`, Hensel square root `sqrtFull` with
              `Zp.SqrtBase`, concrete instances `i₅`, `i₁₃`, `√2 ∈ ℤ_7`.
  · `Field` — `QpSeq` (ℚ_p): add, mul, neg, sub, ofNat, inv, div, sqrt.
  · `DRLT` — 5-adic lift of `N_U = 5^25` for DRLT integration.

All declarations satisfy `#print axioms … → "does not depend on
any axioms"` — see `theory/math/padic_real213.md` for the
narrative and `STRICT_ZERO_AXIOM.md` for the PURE catalog entry.
-/
