# Fibonacci 5-adic valuation — the rank of apparition at the ramified prime

## Overview

`5` is the discriminant of `x² − x − 1`, hence the unique **ramified**
prime of the golden modulus `ℚ(√5) = ℚ(φ)`.  At ramification the
quadratic factors as `x² − x − 1 ≡ (x − 3)² mod 5` — a double root, where
the two Binet branches collapse in status.  This chapter closes, ∅-axiom,
the full 5-adic arithmetic of the Fibonacci sequence at this prime:

- **Rank of apparition** `α(5) = 5`: the first Fibonacci `5` divides is
  `F₅ = 5 = p` itself — the ramified signature (generic primes have
  `α(p) ∣ p ± 1`; only the ramified prime has `α(p) = p`).
- **Singular / regular divergence**: Fibonacci (the singular branch,
  `F_n ≡ n·3ⁿ⁻¹`) vanishes exactly on `5·ℕ`; Lucas (the regular branch,
  `L_n ≡ 2·3ⁿ`) never vanishes mod 5.
- **The all-orders valuation law** `ν₅(F_n) = ν₅(n)`: the
  lifting-the-exponent law, in divisibility form `∀ n k, 5ᵏ ∣ F_n ⟺ 5ᵏ
  ∣ n`.

The same prime `5` is the resolution prime of the fractal-level count
(`configCount 2 = 5²⁵`); this chapter ties it to the *ramified* prime of
the golden modulus the DRLT CKM CP-phase uses (`R_u = 1/φ²`) through one
structural fact — the singular/regular split of the Binet branches at the
double root.

## Lean source

- **Files**:
  - `lean/E213/Lib/Math/NumberTheory/DyadicFSM/FibApparitionMod5.lean`
    (rank of apparition, Lucas-never-zero, the `ν₅ ≥ 1, 2` FSM rungs) —
    20 PURE.
  - `lean/E213/Lib/Math/NumberTheory/FibZIdentities.lean` (integer
    Fibonacci identities → the quintupling identity) — 13 PURE.
  - `lean/E213/Lib/Math/NumberTheory/FibZValuation.lean` (the all-orders
    valuation law) — PURE.
- **Foundations reused**: `fibZ` (`Analysis/Cauchy/OrbitDimension`),
  `ring_intZ` (`Meta/Int213`), Euclid for a prime over `ℤ`/`ℕ`
  (`PolyRoot/IntEuclid`, `ModArith/MarkovPrimeFactor`), the period-20
  Fibonacci FSM (`DyadicFSM/Fib/FSMmod`).
- **∅-axiom status**: 0 DIRTY.

## Narrative

### The FSM rungs (fixed prime powers)

The Fibonacci FSM mod `5` has Pisano period `20 = 4·5`, and its zero-set
within one period is exactly `{0, 5, 10, 15}` — the multiples of `5`.
Reducing any index modulo the period and checking the residues
(`fibMod5_zero_iff`) gives the rank statement `five_dvd_fib_iff`: `5 ∣ F_n
⟺ 5 ∣ n`.  One prime power up, the FSM mod `25` has Pisano period
`100 = 4·5²` with zeros at the multiples of `25`
(`twentyfive_dvd_fib_iff`: `25 ∣ F_n ⟺ 25 ∣ n`, the `ν₅ ≥ 2` reading).
Each rung is a separate finite check; the FSM cannot deliver the all-`k`
law in one stroke — that needs lifting-the-exponent.

Lucas, with the same recurrence but initial conditions `(2, 1)`, has
period `4 = p − 1` mod 5 and never hits `0` (`lucasMod5_never_zero`).
This is the regular Binet branch `L_n ≡ 2·3ⁿ` versus Fibonacci's singular
`F_n ≡ n·3ⁿ⁻¹` at the double root `α ≡ β ≡ 3` — proved at the FSM level
in `fib_lucas_apparition_divergence`.

### The integer engine — the quintupling identity

Over `ℤ` (`fibZ`), built on `ring_intZ`:
- `fibZ_add` — the addition formula `F_{m+n+1} = F_{m+1}F_{n+1} + F_m F_n`
  (two-step induction).
- `fibZ_shift` — the composition law `F_{j+m} = F_{j+1}F_m + F_j(F_{m+1} −
  F_m)`.
- `lucasZ`, `lucasZ_sq` — `L_m = 2F_{m+1} − F_m`, `L_m² = 5F_m² +
  4(−1)ᵐ`; `fibZ_cassini_eps` — the Cassini sign `F_{m+1}² − F_m F_{m+1} −
  F_m² = (−1)ᵐ`.
- `fibZ_index_rec` — the index-multiplication recurrence `F_{b+2m} = L_m
  F_{b+m} − (−1)ᵐ F_b` (a *pure* polynomial identity once `(−1)ᵐ` is the
  Cassini value).
- `fibZ_quintuple` — iterating the index recurrence to `k = 4` gives
  `F_{5m} = (L⁴ − 3εL² + ε²)F_m`; with `ε² = 1` and `L² = 5F² + 4ε` the
  bracket collapses to `F_{5m} = F_m·(25F_m⁴ + 25(−1)ᵐF_m² + 5)`.
- `fibZ_quintuple_factored` — the same as `F_{5m} = 5·(C_m·F_m)` with
  cofactor `C_m = 5F_m⁴ + 5(−1)ᵐF_m² + 1 ≡ 1 mod 5`.

### The lift and the all-orders law

The whole law reduces to the lift `ν₅(F_{5m}) = ν₅(F_m) + 1`.  The
factored quintupling supplies the single factor of `5`; the cofactor `C_m
≡ 1 mod 5` is coprime to `5`, so by Euclid for the prime `5`
(`cop_cancel` via `dvd_prime_pow_cases` + `euclid_of_coprime`) it
contributes no further power.  In divisibility form, `lift`:
`5^{j+1} ∣ F_{5m} ⟺ 5ʲ ∣ F_m`, and `lift_index`: `5^{j+1} ∣ 5m ⟺ 5ʲ ∣
m`.  Strong induction on `n` (`fibN_val_law`) — the `5 ∤ n` branch from
the rank, the `5 ∣ n` branch (`n = 5m`, `m < n`) chaining `lift`, the
induction hypothesis, and `lift_index` — closes `∀ n k, 5ᵏ ∣ F_n ⟺ 5ᵏ ∣
n`, i.e. `ν₅(F_n) = ν₅(n)`.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `five_dvd_fib_iff` | `FibApparitionMod5` | `5 ∣ F_n ⟺ 5 ∣ n` (rank `α(5)=5`) |
| `rank_apparition_five` | `FibApparitionMod5` | `5 ∣ F₅` and no smaller positive index |
| `lucasMod5_never_zero` | `FibApparitionMod5` | `5 ∤ L_n` for every `n` |
| `twentyfive_dvd_fib_iff` | `FibApparitionMod5` | `25 ∣ F_n ⟺ 25 ∣ n` (`ν₅ ≥ 2`) |
| `fibZ_add` | `FibZIdentities` | addition formula over `ℤ` |
| `fibZ_index_rec` | `FibZIdentities` | `F_{b+2m} = L_m F_{b+m} − (−1)ᵐ F_b` |
| `fibZ_quintuple` | `FibZIdentities` | `F_{5m} = F_m(25F_m⁴+25(−1)ᵐF_m²+5)` |
| `fibN_val_law` | `FibZValuation` | `∀ n k, 5ᵏ ∣ F_n ⟺ 5ᵏ ∣ n` (`ν₅(F_n)=ν₅(n)`) |
| `rank_law_dispatch` | `RankApparition` | `p ∣ F_{p−(5/p)}` (= `α(p) ∣ p−(5/p)`), Legendre-dispatched |
| `shared_golden_field_morphism` | `GoldenFieldBridge` | `x²−x−1` (Binet) ≅ `x²+x−1` (`ℚ(ζ₅)⁺`) under `x↦−x`, one ramified `ℚ(√5)` |

## The general-`p` rank law `α(p) ∣ p − (5/p)`

The `p = 5` ramified rung sits inside the general law, now built from the
Legendre character (`DyadicFSM/RankApparition.lean`, 10 PURE).  The
FSM-walking quadratic character `legendre213 5 p` dispatches the Fibonacci
**entry-point index** `rankIndex p hp = p − (5/p)`:

  * split `(5/p)=+1` ⇒ `p − 1`,  inert `(5/p)=−1` ⇒ `p + 1`,
    ramified `(5/p)=0` ⇒ `p` (= `5`, `α(5)=5`),

and `rank_law_dispatch` gives `p ∣ F_{p−(5/p)}` (= `α(p) ∣ p − (5/p)` via
`p ∣ F_n ⟺ α(p) ∣ n`).  Each branch is discharged through the actual universal
Fibonacci-mod-`p` theorem — split via the `𝔽_p` Binet/FLT bridge
(`binet_F_p_minus_1_zero`), inert via the `𝔽_{p²}` Frobenius FLT
(`fpp1_eq_zero_of_frob_phi`), ramified `p=5` via `rank_apparition_five` — so the
law is *built*, not decided per prime.  This mirrors the Pisano-period dispatch
`UniversalDispatch.universal_dispatch_pellCoeff`; here the read-out is the
entry point rather than the period.

The bridge to the CP-phase's `ℚ(ζ₅)` reading is also closed
(`NumberTheory/GoldenFieldBridge.lean`): the Binet polynomial `x²−x−1` and the
Gaussian-period polynomial `x²+x−1` of `ℚ(ζ₅)⁺` are one `ℚ(√5)` object under
`x ↦ −x`, sharing discriminant `5` and the single ramified prime `5` (see
`theory/essays/synthesis/the_golden_prime.md`).

## Open frontier

None for the prime `5`.  The all-orders valuation lift `ν₅(F_n) = ν₅(n)` and the
general rank law `α(p) ∣ p − (5/p)` are both carried out; the `p`-tupling
analogue of the quintupling identity for a general prime's higher valuation
rungs (`νₚ(F_n)` beyond the entry point) is the remaining generalisation.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.NumberTheory.FibZValuation
python3 tools/scan_axioms.py E213.Lib.Math.NumberTheory.FibZValuation
python3 tools/scan_axioms.py E213.Lib.Math.NumberTheory.FibZIdentities
python3 tools/scan_axioms.py E213.Lib.Math.NumberTheory.DyadicFSM.FibApparitionMod5
```
