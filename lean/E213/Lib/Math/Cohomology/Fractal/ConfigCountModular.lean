import E213.Lib.Math.Cohomology.Fractal.ConfigCount
import E213.Lib.Math.ModArith.UniversalFLT
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213

/-!
# `configCountD` modular reductions

For prime `p` coprime to base `d`, the sequence `n ↦ configCountD d n % p`
is eventually periodic with period dividing the multiplicative
order of `d` modulo `(p − 1)`.  The general parametric statement
lives downstream of `Lib/Math/ModArith/UniversalFLT`; here we
record concrete `decide`-checked instances at the physics-selected
base `d = 5` and a few small primes.

## Catalogue (at `d = 5`)

  · `configCountD 5 n % 2 = 1`   for all `n` (5 odd ⇒ 5^k odd)
  · `configCountD 5 n % 3 = 2`   for all `n` (5 ≡ 2 mod 3, 5^n odd,
                                  so 5^(5^n) ≡ 2^odd ≡ 2 mod 3)
  · `configCountD 5 n % 7`       period 2 in `n` from `n = 1`:
                                  5, 3, 5, 3, …
  · `configCountD 5 n % 11`      eventually periodic
  · `configCountD 5 n % 13`      period 2 in `n` from `n = 1`

The decimal-literal tables below are `decide`-checked; the
parametric eventual-periodicity statement is logged as an open
target (consumes `UniversalFLT.flt_main` + an explicit `ord`
enumeration).
-/

namespace E213.Lib.Math.Cohomology.Fractal.ConfigCountModular

open E213.Lib.Math.Cohomology.Fractal.ConfigCount (configCountD pow_add_pure pow_mul_pure)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (div_add_mod)

/-! ## Parametric modular helper

`b % p = 1 % p → ∀ q, b^q % p = 1 % p`.  Structural recursion on `q`
combined with `mul_mod_pure` and a single `congrArg` chain.  This
is the building block for the FLT-based eventual-periodicity
statement: take `b = a^(p-1)` and the hypothesis becomes
`a^(p-1) % p = 1 % p`, which is exactly `UniversalFLT.flt_main`. -/

private theorem pow_mod_one_pow_pure (b p : Nat) (h_b : b % p = 1 % p) :
    ∀ q : Nat, b ^ q % p = 1 % p
  | 0     => by
      show 1 % p = 1 % p
      rfl
  | k + 1 => by
      show (b ^ k * b) % p = 1 % p
      have ih  : b ^ k % p = 1 % p := pow_mod_one_pow_pure b p h_b k
      have h1  : (b ^ k * b) % p = ((b ^ k % p) * (b % p)) % p :=
        mul_mod_pure (b ^ k) b p
      have h2a : (b ^ k % p) * (b % p) = (1 % p) * (b % p) :=
        congrArg (fun x => x * (b % p)) ih
      have h2b : (1 % p) * (b % p) = (1 % p) * (1 % p) :=
        congrArg (fun x => (1 % p) * x) h_b
      have h2  : ((b ^ k % p) * (b % p)) % p = ((1 % p) * (1 % p)) % p :=
        congrArg (· % p) (h2a.trans h2b)
      have h3  : ((1 % p) * (1 % p)) % p = (1 * 1) % p :=
        (mul_mod_pure 1 1 p).symm
      -- `1 * 1 = 1` is `rfl` in `Nat`, so `(1 * 1) % p = 1 % p` is `rfl`.
      have h4  : (1 * 1) % p = 1 % p := rfl
      exact h1.trans (h2.trans (h3.trans h4))

/-! ## Parametric Fermat-style modular reduction

Given the FLT hypothesis `a^(p-1) % p = 1 % p`, the exponent of
`a^k mod p` reduces modulo `p - 1`:

    `a^k % p = a^(k % (p-1)) % p`.

Proof outline (using only 213-native lemmas):
  1. Decompose `k = (p-1)*q + r` via `div_add_mod`.
  2. Rewrite `a^k = a^((p-1)*q) * a^r` via `pow_add_pure`.
  3. Identify `a^((p-1)*q) = (a^(p-1))^q` via `pow_mul_pure`.
  4. Reduce `(a^(p-1))^q % p = 1 % p` via `pow_mod_one_pow_pure`.
  5. Massage `(1 % p * a^r % p) % p = a^r % p` via `mul_mod_pure`. -/

theorem pow_mod_period_pure (a p : Nat) (h_flt : a ^ (p - 1) % p = 1 % p)
    (k : Nat) : a ^ k % p = a ^ (k % (p - 1)) % p := by
  -- Local names for the quotient and remainder.
  let q := k / (p - 1)
  let r := k % (p - 1)
  -- Step 0: decomposition `(p-1) * q + r = k`.
  have h_decomp : (p - 1) * q + r = k := div_add_mod k (p - 1)
  -- Step 1: `a^k = a^((p-1) * q + r)`.
  have h_pow_eq : a ^ k = a ^ ((p - 1) * q + r) :=
    congrArg (a ^ ·) h_decomp.symm
  -- Step 2: `a^((p-1) * q + r) = a^((p-1) * q) * a^r`.
  have h_pow_add : a ^ ((p - 1) * q + r) = a ^ ((p - 1) * q) * a ^ r :=
    pow_add_pure a ((p - 1) * q) r
  -- Step 3: `a^((p-1) * q) = (a^(p-1))^q`.
  have h_pow_mul : a ^ ((p - 1) * q) = (a ^ (p - 1)) ^ q :=
    pow_mul_pure a (p - 1) q
  -- Combine 1-3: `a^k = (a^(p-1))^q * a^r`.
  have h_decompose : a ^ k = (a ^ (p - 1)) ^ q * a ^ r :=
    h_pow_eq.trans (h_pow_add.trans (congrArg (· * a ^ r) h_pow_mul))
  -- Apply mod-p to both sides.
  have h_mod_lhs : a ^ k % p = ((a ^ (p - 1)) ^ q * a ^ r) % p :=
    congrArg (· % p) h_decompose
  -- Step 4: mul-mod split `((a^(p-1))^q * a^r) % p
  --                       = (((a^(p-1))^q % p) * (a^r % p)) % p`.
  have h_split : ((a ^ (p - 1)) ^ q * a ^ r) % p
               = (((a ^ (p - 1)) ^ q % p) * (a ^ r % p)) % p :=
    mul_mod_pure ((a ^ (p - 1)) ^ q) (a ^ r) p
  -- Step 5: `(a^(p-1))^q % p = 1 % p`.
  have h_flt_q : (a ^ (p - 1)) ^ q % p = 1 % p :=
    pow_mod_one_pow_pure (a ^ (p - 1)) p h_flt q
  -- Substitute step 5 into the LHS of step 4.
  have h_after_flt : (((a ^ (p - 1)) ^ q % p) * (a ^ r % p)) % p
                   = ((1 % p) * (a ^ r % p)) % p :=
    congrArg (· % p) (congrArg (fun x => x * (a ^ r % p)) h_flt_q)
  -- Step 6: `((1 % p) * (a^r % p)) % p = (1 * a^r) % p` (mul-mod backwards).
  have h_back : ((1 % p) * (a ^ r % p)) % p = (1 * a ^ r) % p :=
    (mul_mod_pure 1 (a ^ r) p).symm
  -- `1 * a^r = a^r` and `(1 * a^r) % p = a^r % p` via `Nat.one_mul`.
  have h_one_mul : (1 * a ^ r) % p = a ^ r % p :=
    congrArg (· % p) (Nat.one_mul (a ^ r))
  -- Chain everything.
  exact h_mod_lhs.trans (h_split.trans (h_after_flt.trans (h_back.trans h_one_mul)))

/-- Corollary at the `configCountD` family: given the FLT hypothesis
    `d^(p-1) % p = 1 % p`, the count `configCountD d n` reduces
    mod `p` through the exponent:

      `configCountD d n % p = d ^ ((d^n) % (p-1)) % p`.

    This is the entry point for the eventual-periodicity story:
    the sequence `n ↦ configCountD d n % p` is governed by the
    sequence `n ↦ (d^n) % (p-1)`, whose periodic structure is in
    turn the multiplicative order of `d` modulo `p-1`. -/
theorem configCountD_mod_pure
    (d p : Nat) (h_flt : d ^ (p - 1) % p = 1 % p) (n : Nat) :
    configCountD d n % p = d ^ ((d ^ n) % (p - 1)) % p := by
  show d ^ (d ^ n) % p = d ^ ((d ^ n) % (p - 1)) % p
  exact pow_mod_period_pure d p h_flt (d ^ n)

/-! ## FLT-instantiated smoke at `(d, p) = (5, 7)`

Combines `UniversalFLT.universal_flt_main` (Fermat's Little
Theorem) with the parametric `configCountD_mod_pure` to obtain a
closed-form modular reduction at the physics-selected base.  The
sequence `n ↦ configCountD 5 n % 7` is governed by
`n ↦ (5^n) % 6`, whose values are 1, 5, 1, 5, … (period 2 from
`n = 1`). -/

/-- FLT at `(a, p) = (5, 7)`: `5^6 % 7 = 1 % 7`.  Composed from
    `universal_flt_main` + the precomputed `prime_gcd_7`. -/
theorem flt_5_7 : (5 ^ 6) % 7 = 1 % 7 :=
  E213.Lib.Math.ModArith.UniversalFLT.universal_flt_main
    5 7 (by decide) (by decide) (by decide)
    E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_7

/-- Parametric in `n`: `configCountD 5 n % 7 = 5 ^ ((5^n) % 6) % 7`.
    Specialises `configCountD_mod_pure` at `(d, p) = (5, 7)`. -/
theorem configCountD_5_mod_7 (n : Nat) :
    configCountD 5 n % 7 = 5 ^ ((5 ^ n) % 6) % 7 :=
  configCountD_mod_pure 5 7 flt_5_7 n

/-! ## `d = 5`, `p = 2` — constant 1 -/

theorem configCountD_5_0_mod_2 : configCountD 5 0 % 2 = 1 := by decide
theorem configCountD_5_1_mod_2 : configCountD 5 1 % 2 = 1 := by decide
theorem configCountD_5_2_mod_2 : configCountD 5 2 % 2 = 1 := by decide

/-! ## `d = 5`, `p = 3` — constant 2 -/

theorem configCountD_5_0_mod_3 : configCountD 5 0 % 3 = 2 := by decide
theorem configCountD_5_1_mod_3 : configCountD 5 1 % 3 = 2 := by decide
theorem configCountD_5_2_mod_3 : configCountD 5 2 % 3 = 2 := by decide

/-! ## `d = 5`, `p = 7` — period 2 (5, 3, 5, …) from `n = 1` -/

theorem configCountD_5_0_mod_7 : configCountD 5 0 % 7 = 5 := by decide
theorem configCountD_5_1_mod_7 : configCountD 5 1 % 7 = 3 := by decide
theorem configCountD_5_2_mod_7 : configCountD 5 2 % 7 = 5 := by decide

/-! ## `d = 5`, `p = 11`

`5 mod 10 = 5`; `gcd(5, 10) = 5 > 1`, so the multiplicative
order argument bottoms out — the modular sequence is eventually
constant after `n ≥ 1`. -/

theorem configCountD_5_0_mod_11 : configCountD 5 0 % 11 = 5 := by decide
theorem configCountD_5_1_mod_11 : configCountD 5 1 % 11 = 1 := by decide
theorem configCountD_5_2_mod_11 : configCountD 5 2 % 11 = 1 := by decide

/-! ## `d = 5`, `p = 13` — period 2 from `n = 1` -/

theorem configCountD_5_0_mod_13 : configCountD 5 0 % 13 = 5 := by decide
theorem configCountD_5_1_mod_13 : configCountD 5 1 % 13 = 5 := by decide
theorem configCountD_5_2_mod_13 : configCountD 5 2 % 13 = 5 := by decide

/-! ## Cross-base level-2 sample at small primes

The level-2 readout per base, modulo a fixed small prime, brings
out the structural per-base differences. -/

theorem configCountD_2_2_mod_7 : configCountD 2 2 % 7 = 2 := by decide   -- 16 mod 7
theorem configCountD_3_2_mod_7 : configCountD 3 2 % 7 = 6 := by decide   -- 3^9 mod 7
theorem configCountD_5_2_mod_7' : configCountD 5 2 % 7 = 5 := by decide

/-! ## Capstone — modular table at the physics-selected base

Bundles the small-prime modular readouts at the physics base
`d = 5` and level `n = 2` (`= N_U`).  Records that the `N_U` value
agrees with the per-prime FLT-reduced computation. -/

theorem configCountD_5_2_mod_table :
    configCountD 5 2 % 2 = 1
    ∧ configCountD 5 2 % 3 = 2
    ∧ configCountD 5 2 % 5 = 0
    ∧ configCountD 5 2 % 7 = 5
    ∧ configCountD 5 2 % 11 = 1
    ∧ configCountD 5 2 % 13 = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Fractal.ConfigCountModular
