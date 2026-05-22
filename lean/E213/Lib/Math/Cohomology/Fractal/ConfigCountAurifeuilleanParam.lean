import E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuillean
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213

/-!
# Parametric Aurifeuillean handle: `∀ n ≥ 1, 521 ∣ 5^(5^n) + 1`

Establishes the *n-uniform* Aurifeuillean divisibility:

```
∀ m, (5^(5^(m+1)) + 1) % 521 = 0.
```

Equivalent reading: for every `n ≥ 1`,
`5^(5^n) ≡ −1 (mod 521)`, hence `521 ∣ 5^(5^n) + 1`.

The proof is a clean induction on `m`:
  · **Base** `m = 0`: `5^(5^1) = 5^5 = 3125 = 6 · 521 − 1`, so
    `5^5 % 521 = 520`.  Discharged by `decide`.
  · **Step** `m + 1`: rewrite
    `5^(5^(m+2)) = 5^(5^(m+1) · 5) = (5^(5^(m+1)))^5` via
    `pow_mul_pure`, then apply the auxiliary `pow_mod_base`
    (which says `a^k % p = (a % p)^k % p`) to reduce inside the
    outer `^5`, use the inductive hypothesis to replace
    `5^(5^(m+1)) % 521` by `520`, and finish with the decidable
    seed `520^5 % 521 = 520` (since `520 ≡ −1 (mod 521)` and
    `(−1)^5 = −1`).

No FLT, no period reduction, no Carmichael — the structural seed
`5^5 ≡ −1 (mod 521)` (i.e., `Φ_10(5) = 521` divides `5^5 + 1`
exactly) does all the work, propagated by the algebraic identity
`5^(5^(n+1)) = (5^(5^n))^5`.
-/

namespace E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuilleanParam

open E213.Lib.Math.Cohomology.Fractal.ConfigCount
  (configCount configCountD pow_mul_pure)
open E213.Meta.Nat.MulMod213 (mul_mod_pure mul_mod_left_pure)
open E213.Meta.Nat.AddMod213 (add_mod_gen)

/-! ## §1 Auxiliary: `(a^k) % p = ((a % p)^k) % p`

Reduces a power `mod p` by first reducing the base.  Plain
induction on `k`, with the inductive step assembled from
`mul_mod_pure` and `mul_mod_left_pure`. -/

private theorem pow_mod_base (a p : Nat) : ∀ k, a^k % p = (a % p)^k % p
  | 0     => rfl
  | k + 1 => by
      show (a^k * a) % p = ((a % p)^k * (a % p)) % p
      have ih : a^k % p = (a % p)^k % p := pow_mod_base a p k
      calc (a^k * a) % p
          = (a^k % p * (a % p)) % p := mul_mod_pure (a^k) a p
        _ = ((a % p)^k % p * (a % p)) % p := by rw [ih]
        _ = ((a % p)^k * (a % p)) % p :=
              (mul_mod_left_pure ((a % p)^k) (a % p) p).symm

/-! ## §2 Decidable seeds

The two numerical inputs to the induction. -/

/-- Aurifeuillean seed: `5^5 ≡ 520 ≡ −1 (mod 521)`.  Equivalent
    to `5^5 + 1 = 6 · 521`.  Decidable: `3125 % 521 = 520`. -/
private theorem five_pow_5_mod_521 : 5^5 % 521 = 520 := by decide

/-- Inductive-step seed: `520^5 ≡ 520 (mod 521)`.  Decidable:
    since `520 ≡ −1 (mod 521)` and `(−1)^5 = −1`,
    `520^5 % 521 = 520`. -/
private theorem five20_pow_5_mod_521 : 520^5 % 521 = 520 := by decide

/-! ## §3 Parametric divisibility

The main theorem.  Stated over `m = n − 1` so that the
`n ≥ 1` precondition is built into the indexing. -/

/-- For every `m`, `5^(5^(m+1)) ≡ 520 ≡ −1 (mod 521)`.

    Equivalently: for every `n ≥ 1`, `521 ∣ 5^(5^n) + 1`. -/
theorem five_pow_five_pow_succ_mod_521 :
    ∀ m, 5^(5^(m+1)) % 521 = 520
  | 0     => five_pow_5_mod_521
  | m + 1 => by
      have ih : 5^(5^(m+1)) % 521 = 520 :=
        five_pow_five_pow_succ_mod_521 m
      -- `5^(m+2) = 5^(m+1) * 5` is definitional (Nat.pow_succ).
      have h_exp : 5^(m+2) = 5^(m+1) * 5 := rfl
      -- `5^(5^(m+1) * 5) = (5^(5^(m+1)))^5` by pow_mul_pure.
      have h_pow : 5^(5^(m+1) * 5) = (5^(5^(m+1)))^5 :=
        pow_mul_pure 5 (5^(m+1)) 5
      show 5^(5^(m+2)) % 521 = 520
      -- After this rewrite chain, the goal reduces to `520^5 % 521 = 520`,
      -- which Lean closes by kernel computation (the content of
      -- `five20_pow_5_mod_521`).
      rw [h_exp, h_pow, pow_mod_base (5^(5^(m+1))) 521 5, ih]

/-! ## §4 Aurifeuillean handle (n-uniform) -/

/-- ★ **N_U-family Aurifeuillean handle, parametric in `n ≥ 1`**:

    For every `m`, `521 ∣ 5^(5^(m+1)) + 1`,
    i.e. `521 ∣ configCount (m+1) + 1`.

    This is the universal divisibility statement: the prime
    `521 = Φ_10(5) = N(29 + 8√5) ∈ ℤ[√5]` is the unique
    Aurifeuillean cyclotomic factor of the sequence
    `5^(5^n) + 1`, and it appears uniformly across all `n ≥ 1`. -/
theorem aurifeuillean_universal :
    ∀ m, (configCount (m + 1) + 1) % 521 = 0 := by
  intro m
  show (5^(5^(m+1)) + 1) % 521 = 0
  have h : 5^(5^(m+1)) % 521 = 520 :=
    five_pow_five_pow_succ_mod_521 m
  -- `(a + 1) % p = ((a % p) + (1 % p)) % p` via add_mod_gen.
  -- After the rewrites, the goal reduces to `(520 + 1) % 521 = 0`,
  -- which Lean closes by kernel computation (`521 % 521 = 0`).
  rw [add_mod_gen (5^(5^(m+1))) 1 521, h]

/-! ## §5 Specialisations -/

/-- `n = 1` specialisation: `521 ∣ 5^5 + 1`.  Instantiates the
    parametric statement at `m = 0`. -/
theorem aurifeuillean_at_n_eq_1 :
    (configCount 1 + 1) % 521 = 0 :=
  aurifeuillean_universal 0

/-- `n = 2` specialisation (the physics slice, `N_U + 1`):
    `521 ∣ 5^25 + 1`.  Instantiates the parametric statement
    at `m = 1`. -/
theorem aurifeuillean_at_n_eq_2 :
    (configCount 2 + 1) % 521 = 0 :=
  aurifeuillean_universal 1

/-- `n = 3` specialisation: `521 ∣ 5^125 + 1`.  Instantiates the
    parametric statement at `m = 2`.  Notable for avoiding the
    88-digit `decide` of the concrete instance — the inductive
    proof completes in 3 steps regardless of `n`. -/
theorem aurifeuillean_at_n_eq_3 :
    (configCount 3 + 1) % 521 = 0 :=
  aurifeuillean_universal 2

end E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuilleanParam
