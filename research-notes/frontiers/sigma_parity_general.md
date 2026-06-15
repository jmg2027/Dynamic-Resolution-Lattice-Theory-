# Frontier: σ(n) parity — the general ⟺ (square or twice-square)

**Status**: partial closed (`lean/E213/Lib/Math/NumberTheory/SigmaParity.lean`, 13 PURE).
General ⟺ blocked on missing corpus infra.

## Target
`σ(n)` odd ⟺ `n` is a perfect square or twice a perfect square.

## Closed (general, PURE) in `SigmaParity.lean`
- `sigma_two_pow_odd k : sigma (2^k) % 2 = 1` (general k).
- `sigma_odd_prime_pow_parity (Prime213 p) (p%2=1) k : sigma (p^k) % 2 = (k+1) % 2`
  — the multiplicative heart (σ(pᵏ)=Σ_{i≤k}pⁱ, each pⁱ odd ⇒ parity = term count).
- `sigma_three_pow_parity`, even-exponent prime-power square cases, and the
  `sigma_parity_table` (n=1..30 matching the square-or-twice-square indicator).

## The three missing corpus crux lemmas (block the general ⟺)
1. **No 2-adic odd-part decomposition** `n = 2^a · odd` (no `oddPart` / `ord_compl` /
   `exists_two_pow_mul_odd` under `lean/E213`).
2. **No `isSquare_iff_all_vp_even`** ("perfect square ⟺ every prime valuation even").
   `Meta/Nat/VpSeparation.vp_separation` proves *injectivity* of the exponent vector,
   not the square criterion.
3. **No general `sigma`-over-factorization chain** — `DivisorMultiplicative.sigma_mul`
   is binary/coprime only; no induction folding it over a full factorization.

## Path to close
Build (1) `n = 2^(v₂ n) · oddPart n` with `oddPart` odd, (2) `IsSquare n ↔ ∀ p, 2 ∣ vp p n`
from `vp` + UFD, (3) a multiplicative-fold `σ(∏ pᵢ^kᵢ) = ∏ σ(pᵢ^kᵢ)`. Then σ(n) odd ⟺
every odd-prime exponent even ⟺ oddPart n is a square ⟺ n = square or twice-square.
These three are reusable beyond σ-parity (τ-parity's multiplicative route, Euler perfect
converse, etc.) — a worthwhile infra investment, not σ-specific.
