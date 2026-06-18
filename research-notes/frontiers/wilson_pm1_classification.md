# Frontier: Gauss-Wilson ±1 value classification

`NumberTheory/WilsonGeneralization` (29 PURE) closed the **inverse-pairing core**:
`units_prod_eq_selfinv_prod` (∏ units of ℤ/n = ∏ self-inverse units, via the
involution `u ↦ unitInv n u`), `unitInv_eq_self_iff` (self-inverse ⟺ u²≡1), prime
recovery, and Gauss +1/−1 smokes.

**Progress:** `NumberTheory/WilsonValue` (13 PURE) closed the **−1 value direction**
`wilson_neg_one_of_sqrt_trivial`: `∏(units of ℤ/n) ≡ −1` when ±1 are the only square
roots of 1 (the self-inverse set is then exactly {1, n−1}); recovers Wilson's `(p−1)!≡−1`
from the units side. Still open (the value classification):** `∏(units of ℤ/n) ≡ −1 (mod n) ⟺ n ∈
{1,2,4,pᵏ,2pᵏ}` (i.e. ⟺ (ℤ/n)^× is cyclic, with a unique element of order 2).
Remaining work: characterize the self-inverse units (solutions of x²≡1 mod n) by
CRT/the prime-power structure — for n=2pᵏ or pᵏ there are exactly two (1 and −1),
product −1; for n with ≥2 odd prime factors or 8∣n there are ≥4, paired off to
product +1. Reuses `units_prod_eq_selfinv_prod` + a count/structure of √1 mod n.
QR/CRT-structure heavy; do interactively.


## Progress (after SqrtOnePrimePower)
`NumberTheory/SqrtOnePrimePower` (7 PURE): `sqrt_one_prime_power` — for odd prime p,
the only square roots of 1 mod pᵏ are ±1 (vp argument: vp_p((x−1)(x+1)) ≥ k with min = 0
since p∤2 ⟹ pᵏ divides one factor); hence `wilson_neg_one_prime_power : ∏(units of ℤ/pᵏ)
≡ −1`. The `n = pᵏ` (odd) case of the −1 classification is DONE. `NumberTheory/SqrtOneTwoPrimePower`
(9 PURE): `sqrt_one_two_prime_power` (n=2pᵏ via CRT/parity ⟹ only ±1) + `wilson_neg_one_four`
+ `sqrt_one_coprime`. **The −1 ⟸ direction is now complete: n ∈ {1,2,4,pᵏ,2pᵏ} ⟹ ∏ units ≡ −1**
(pᵏ, 2pᵏ via the keystones; 1,2,4 trivial/decide).

## Residual (after WilsonValue + SqrtOnePrimePower)
1. **+1 direction**: `#√1 ≥ 4 ⟹ ∏ units ≡ +1` (the √1 form an elementary-abelian
   2-group; product of all elements = identity when rank ≥ 2).
2. **CRT count**: `#√1 mod n = 2 ⟺ n ∈ {1,2,4,pᵏ,2pᵏ}` (odd pᵏ DONE; remaining: 2pᵏ via CRT(2,pᵏ), n=4, and the composite/2ᵃ a≥3 → ≥4 roots side) (√1-count via CRT over the
   prime-power factorization). Together these discharge `htriv`/its negation from n's
   factorization, completing the ⟺.


## +1 existence side DONE (WilsonPlusOne + WilsonExistence)
`NumberTheory/WilsonPlusOne` (17 PURE, the research-verified argument `∏√1 ≡ 1` when |S|≥4, via `P ≡ t^(|S|/2)` + parity, no group theory) + `NumberTheory/WilsonExistence` (13 PURE): a nontrivial √1 exists via `crtSolve(1,−1)` for any coprime split n=a·b (a,b>2), and via `2^(a−1)−1` for n=2^a (a≥3) ⟹ `∏(units) ≡ +1`. **The value dichotomy is complete** (`∏ units ≡ −1 ⟺ only ±1 are √1` / `≡ +1 ⟺ ∃ nontrivial √1`). **Residual for the full `⟺ n∈{1,2,4,pᵏ,2pᵏ}`:** only the finicky `n`-factorization case-split (every n∉{1,2,4,pᵏ,2pᵏ} is a coprime split with both factors >2, or 2^a a≥3) — routine assembly, not research.
