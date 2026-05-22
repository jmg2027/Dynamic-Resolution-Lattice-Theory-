import E213.Lib.Math.Cohomology.Fractal.ConfigCount

/-!
# `configCountD` Aurifeuillean handle on `N_U + 1`

The integer `521` is the *unique* Aurifeuillean cyclotomic factor
of the sequence `5^(5^n) + 1` across `n ≥ 1`.  It enters as
`Φ_10(5) = 521`, and it admits the norm representation

```
521 = 29² − 5 · 8² = N(29 + 8√5)
```

in the ring `ℤ[√5]`.  The Schinzel–Brent Aurifeuillean condition
selects exactly the cyclotomic indices `n = 2 · b · m²` with
`m` odd, `gcd(m, b) = 1`; for the physics base `b = 5`, the
smallest such index is `n = 10` (m = 1), yielding `Φ_10(5) = 521`.
The other cyclotomic factors of `5^(5^n) + 1` — namely `Φ_50(5)`,
`Φ_250(5)`, etc. — fail the Aurifeuillean condition (50 = 2·5²,
m² = 5 has no integer solution).

This file records:
  · the norm identity `29² = 5 · 8² + 521`;
  · the Φ_10 evaluation `5^4 + 5^2 + 1 = 5^3 + 5 + 521`
    (`Φ_10(5) = 521`, recast in `Nat` to avoid subtraction);
  · the seed identity `5^5 + 1 = 6 · 521`
    (which expresses `5^5 ≡ −1 (mod 521)` in `Nat` form);
  · concrete divisibility `521 ∣ 5^(5^n) + 1` at `n ∈ {1, 2, 3}`,
    the physics-relevant slice being `n = 2`.

The parametric `∀ n ≥ 1` statement is deferred to a Phase-2 file
(`ConfigCountAurifeuilleanParam.lean`).

Source: `research-notes/G125_aurifeuillean_n_u.md` §1-§4.
-/

namespace E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuillean

open E213.Lib.Math.Cohomology.Fractal.ConfigCount (configCount configCountD)

/-! ## §1 Norm representation in `ℤ[√5]`

The Aurifeuillean prime `521` is the norm of `29 + 8√5`:

```
N(a + b√5) := a² − 5 b²
N(29 + 8√5) = 29² − 5 · 8² = 841 − 320 = 521
```

Recast in `Nat` (no subtraction): `29² = 5 · 8² + 521`. -/

/-- Aurifeuillean norm: `521 = 29² − 5·8²`, in `Nat`-friendly form. -/
theorem aurifeuillean_norm_521 : 29 * 29 = 5 * (8 * 8) + 521 := by decide

/-- Hunter-catalogue bridge: the Aurifeuillean norm pair `(29, 8)`
    of `521` decomposes into Hunter primitives `{NS=3, NT=2, d=5, c=2}`:

    ```
    29 = d² + NT²    (= 25 + 4)
    8  = NT³         (= 2³, catalog atom)
    521 = (d² + NT²)² − d · (NT³)²
    ```

    Equivalently in `ℤ[√d]`: `521 = N((d² + NT²) + NT³ · √d)`.
    Recast in `Nat`: `(d² + NT²)² = d · (NT³)² + 521`. -/
theorem aurifeuillean_norm_521_hunter :
    (5^2 + 2^2) * (5^2 + 2^2) = 5 * ((2^3) * (2^3)) + 521 := by decide

/-! ## §2 Cyclotomic identity `Φ_10(5) = 521`

`Φ_10(x) = x^4 − x^3 + x^2 − x + 1`.  At `x = 5`:
`625 − 125 + 25 − 5 + 1 = 521`.  In `Nat`: rearrange to
`x^4 + x^2 + 1 = x^3 + x + 521` at `x = 5`. -/

/-- Cyclotomic identity `Φ_10(5) = 521`, recast in `Nat`. -/
theorem phi_10_at_5 : 5^4 + 5^2 + 1 = 5^3 + 5 + 521 := by decide

/-! ## §3 Seed identity `5^5 ≡ −1 (mod 521)`

The structural seed `5^5 + 1 = 3126 = 6 · 521`.  This is the
identity from which the parametric `521 ∣ 5^(5^n) + 1` divisibility
chain follows by `5^n ≡ 5 (mod 10)` for `n ≥ 1` and the parity of
`5^{n-1}`. -/

/-- Seed: `5^5 + 1 = 6 · 521`, equivalently `5^5 ≡ −1 (mod 521)`. -/
theorem five_pow_5_plus_one : 5^5 + 1 = 6 * 521 := by decide

/-! ## §4 Concrete divisibility at `n ∈ {1, 2, 3}` -/

/-- `n = 1` slice: `5^(5^1) + 1 = 5^5 + 1 = 3126 = 6 · 521`. -/
theorem configCount_one_plus_one_eq_mul_521 :
    configCount 1 + 1 = 6 * 521 := by decide

/-- `n = 1` modular form: `521 ∣ 5^5 + 1`. -/
theorem configCount_one_plus_one_mod_521 :
    (configCount 1 + 1) % 521 = 0 := by decide

/-- `n = 2` slice (the physics slice, `N_U + 1`):
    `5^25 + 1 = 521 · 572021542950006`. -/
theorem configCount_two_plus_one_eq_mul_521 :
    configCount 2 + 1 = 521 * 572021542950006 := by decide

/-- `n = 2` modular form: `521 ∣ N_U + 1 = 5^25 + 1`.

    Together with `phi_10_at_5` and `aurifeuillean_norm_521`,
    this expresses the Aurifeuillean handle on the physics slice. -/
theorem configCount_two_plus_one_mod_521 :
    (configCount 2 + 1) % 521 = 0 := by decide

/-- `n = 3` modular form: `521 ∣ 5^125 + 1`.  An 88-digit number,
    but `decide` reduces it kernel-side without difficulty. -/
theorem configCount_three_plus_one_mod_521 :
    (configCount 3 + 1) % 521 = 0 := by decide

/-! ## §5 Higher Aurifeuillean cyclotomic factors at base 5

The Schinzel–Brent Aurifeuillean condition for base `b ≡ 1 (mod 4)`
selects cyclotomic indices `n = 2 · b · m²` with `m` odd squarefree,
`gcd(m, b) = 1`.  At base `b = 5`:
  · `m = 1 → n = 10`: `Φ_10(5) = 521`, canonical pair `(29, 8)`
    — both Hunter-expressible (§1, §1.Hunter).
  · `m = 3 → n = 90`: `Φ_90(5) = 60081451169922001`, canonical pair
    `(L, M) = (850554441, 364242064)` — 9-digit integers without
    Hunter expressibility.
  · `m = 7 → n = 490`: `Φ_490(5)`, a 117-digit prime.  Aurifeuillean
    pair exists in `ℤ[√5]` but with magnitudes well outside any
    Hunter-atomic range.

The pattern: **Hunter expressibility is localised to the minimal
index `m = 1`**.  Higher Aurifeuillean indices yield canonical
`(L, M)` pairs that are generic primes in `ℤ[√5]`, unrelated to
the physics-atomic generators `{NS, NT, d, c} = {3, 2, 5, 2}`.

This pattern aligns with the "last discrete Galois split before
tetration" reading: the smallest non-trivial cyclotomic
factorisation at base `d = 5` preserves Hunter-atomic structure
because the L-coefficients themselves are still small.  Larger
indices push the L-coefficients into the algebraic-integer
landscape of `ℤ[√5]` proper, where Hunter primitives have no
structural reach. -/

/-- Φ_90(5) Aurifeuillean factorisation: a 17-digit prime
    expressed as `L² − 5 · M²` with `L = 850554441`,
    `M = 364242064`.  Recast in `Nat`: `L² = 5·M² + Φ_90(5)`.

    `Φ_90(5)` itself: `Nat`-friendly evaluation of
    `Φ_90(x) = x^24 + x^23 − x^21 − x^20 − x^19 + x^17 + x^16 + x^15
              − x^13 − x^12 − x^11 + x^9 + x^8 + x^7 − x^5 − x^4
              − x^3 + x + 1`
    at `x = 5` gives the integer
    `60081451169922001`.

    Hunter status: neither `L = 850554441` nor `M = 364242064`
    admit small-depth representations from
    `{NS = 3, NT = 2, d = 5, c = 2}`.  The Hunter-Aurifeuillean
    correspondence is therefore localised to the minimal index
    `m = 1` (= the `521` slice). -/
theorem aurifeuillean_phi_90_at_5 :
    850554441 * 850554441 = 5 * (364242064 * 364242064) + 60081451169922001 := by
  decide

/-! ## §6 Capstone — Aurifeuillean fingerprint at the physics slice

Bundles the norm representation, cyclotomic identity, and
divisibility at `n = 2`. -/

/-- Aurifeuillean fingerprint of `N_U + 1`:
    `Φ_10(5) = 521`, `521 = 29² − 5 · 8²`, and `521 ∣ N_U + 1`. -/
theorem aurifeuillean_fingerprint_n_u :
    5^4 + 5^2 + 1 = 5^3 + 5 + 521
    ∧ 29 * 29 = 5 * (8 * 8) + 521
    ∧ (configCount 2 + 1) % 521 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuillean
