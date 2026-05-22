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

/-! ## §5 Capstone — Aurifeuillean fingerprint at the physics slice

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
