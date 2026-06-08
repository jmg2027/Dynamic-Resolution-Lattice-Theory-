import E213.Lib.Math.NumberSystems.Padic.Foundation
import E213.Lib.Math.NumberSystems.Padic.Arith
import E213.Lib.Math.NumberSystems.Padic.Pow
import E213.Lib.Math.NumberSystems.Padic.Norm
import E213.Lib.Math.NumberSystems.Padic.Hensel
import E213.Lib.Math.NumberSystems.Padic.Teichmuller
import E213.Lib.Math.NumberSystems.Padic.TeichmullerUnit
import E213.Lib.Math.NumberSystems.Padic.Field
import E213.Lib.Math.NumberSystems.Padic.DRLT
import E213.Lib.Math.NumberSystems.Padic.NuEscape
import E213.Lib.Math.NumberSystems.Padic.SetoidMul
/-!
# Real213-p-adic — umbrella import

The full p-adic number library, 213-native and ∅-axiom.

Sub-modules:
  · `Foundation` — `ZpSeq`, truncation, base-p digit embedding.
  · `Arith` — addition, negation, multiplication with carry FSM;
              ring-quotient theorems `add_trunc` / `mul_trunc`;
              full ring axioms at trunc (incl. `add_neg_self_trunc`).
  · `Pow` — natural-number power `Zp.pow x n` with trunc homomorphism
              (`pow_trunc`, `pow_add_trunc`, `pow_mul_trunc`); Fermat
              at digit 0 (`pow_p_trunc_one`); `teichmuller_iter`.
  · `Norm` — `valAtLeast` / `valEq` + full strong ultrametric
              (additive + multiplicative + negation, precise valEq
              forms `valEq_add_of_lt`, `valEq_mul`, `valEq_neg`).
  · `Hensel` — Bezout-based digit-0 inverse + Hensel-lifted full
              inverse `invFull` (with `inv_trunc_unique`); Hensel
              sqrt `sqrtFull` with `SqrtBase` (with `sqr_unique_trunc`);
              cancellation laws; concrete instances `i₅`, `i₁₃`,
              `√2 ∈ ℤ_7`.
  · `Teichmuller` — `frobenius_lift` (`y ≡ z mod p^k → y^p ≡ z^p
              mod p^(k+1)`, any `p ≥ 1`); `teichmuller_iter_cauchy`
              (Cauchy property of `x ↦ x^p` iteration); the explicit
              representative `teichmuller` (`ω(x)`, diagonal limit) with
              the Frobenius fix `teichmuller_pow_p_trunc` (`ω^p ≡ ω`).
  · `TeichmullerUnit` — `ω(x)` as a `(p−1)`-th root of unity
              (`teichmuller_pow_pred_trunc`, `ω^(p−1) ≡ 1`) and the
              principal-unit decomposition `x = ω(x) · u`
              (`teichmullerCofactor`, `u ≡ 1 mod p`) — the
              `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)` split.
  · `Field` — `QpSeq` (ℚ_p): add, sub, mul, neg, ofNat, inv, div, sqrt.
  · `DRLT` — canonical 5-adic embeddings (`ℕ ↪ ZpSeq 5`).

All declarations satisfy `#print axioms … → "does not depend on
any axioms"` — see `theory/math/numbersystems/padic_real213.md` for the
narrative and `STRICT_ZERO_AXIOM.md` for the PURE catalog entry.
-/
