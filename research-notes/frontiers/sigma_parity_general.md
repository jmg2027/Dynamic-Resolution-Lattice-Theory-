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
1. ~~**No 2-adic odd-part decomposition** `n = 2^a · odd`.~~ **CLOSED** (iter 164,
   `lean/E213/Lib/Math/NumberTheory/OddPartDecomposition.lean`): `decomp : n = 2^(v2 n)·oddPart n`,
   `oddPart_odd`, `sigma_decomp : σ n = σ(2^(v2 n))·σ(oddPart n)`, and
   `sigma_odd_iff_oddPart : σ n % 2 = 1 ↔ σ(oddPart n) % 2 = 1` — the general σ-parity ⟺ now reduces
   to a statement about `oddPart n` only.  Remaining: crux #2 below.
2. **No `isSquare_iff_all_vp_even`** ("perfect square ⟺ every prime valuation even").
   PARTIALLY ADDRESSED (iter 165, `SquareCharacterization.lean`): the 2-adic half is done —
   `coprime_isSquare_mul` (coprime `u,v` ⟹ `IsSquare(uv) ↔ IsSquare u ∧ IsSquare v`, GENERAL,
   pure-gcd route, NO UFD), `isSquare_two_pow_iff` (`IsSquare(2^a) ↔ a even`),
   `isSquare_iff` (`IsSquare n ↔ v2 n even ∧ IsSquare(oddPart n)`), and the σ-parity bridge
   `sq_or_twice_iff` (`(n square ∨ n twice-square) ↔ IsSquare(oddPart n)`).  Still missing: the
   full odd-prime-valuation criterion for the ODD part.
3. **No general `sigma`-over-factorization chain** — `DivisorMultiplicative.sigma_mul`
   is binary/coprime only; no induction folding it over a full factorization.

## Frontier reduced to ONE lemma (after iters 162, 164, 165)
Combining `sigma_odd_iff_oddPart` (164: σ(n) odd ⟺ σ(oddPart n) odd) and `sq_or_twice_iff`
(165: n square-or-twice-square ⟺ oddPart n square), the general σ-parity ⟺ now reduces to **exactly**:
> **`sigma_odd_square_odd`**: for ODD `m`, `σ(m) % 2 = 1 ↔ IsSquare m`.
This is the remaining crux #3 (the multiplicative fold of `sigma_odd_prime_pow_parity` (162) over the
odd factorization, + `isSquare` of an odd number ⟺ all its odd-prime exponents even).  Closing this one
lemma closes the whole theorem `σ(n) odd ⟺ n square or twice-square`.

## Path to close
Build (1) `n = 2^(v₂ n) · oddPart n` with `oddPart` odd, (2) `IsSquare n ↔ ∀ p, 2 ∣ vp p n`
from `vp` + UFD, (3) a multiplicative-fold `σ(∏ pᵢ^kᵢ) = ∏ σ(pᵢ^kᵢ)`. Then σ(n) odd ⟺
every odd-prime exponent even ⟺ oddPart n is a square ⟺ n = square or twice-square.
These three are reusable beyond σ-parity (τ-parity's multiplicative route, Euler perfect
converse, etc.) — a worthwhile infra investment, not σ-specific.
