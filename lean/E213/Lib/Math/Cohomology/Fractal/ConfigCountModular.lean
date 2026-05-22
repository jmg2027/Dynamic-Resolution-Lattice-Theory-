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
open E213.Meta.Nat.MulMod213 (mul_mod_pure mul_mod_left_pure)
open E213.Meta.Nat.AddMod213 (div_add_mod mod_mod)

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

/-! ## Eventual periodicity at `(d, p) = (5, 7)`

The multiplicative order of `5` modulo `6` is `2` (since
`5^2 = 25 ≡ 1 mod 6`).  Combined with the parametric reduction
`configCountD 5 n % 7 = 5^((5^n) % 6) % 7`, this gives a clean
period-2 statement on the family at the physics-selected base. -/

/-- General order-2 step: if `a^2 ≡ 1 (mod b)`, then
    `a^(n+2) ≡ a^n (mod b)`.  Used for primes `p` where the
    multiplicative order of the base modulo `p - 1` is 2. -/
private theorem pow_add_two_mod_pure (a b : Nat) (h_sq : a ^ 2 % b = 1)
    (n : Nat) : a ^ (n + 2) % b = a ^ n % b := by
  have h_pow_add : a ^ (n + 2) = a ^ n * a ^ 2 := pow_add_pure a n 2
  have h_mod_eq : a ^ (n + 2) % b = (a ^ n * a ^ 2) % b :=
    congrArg (· % b) h_pow_add
  have h_split : (a ^ n * a ^ 2) % b = ((a ^ n % b) * (a ^ 2 % b)) % b :=
    mul_mod_pure (a ^ n) (a ^ 2) b
  have h_simp : ((a ^ n % b) * (a ^ 2 % b)) % b = ((a ^ n % b) * 1) % b :=
    congrArg (· % b) (congrArg ((a ^ n % b) * ·) h_sq)
  have h_one : ((a ^ n % b) * 1) % b = (a ^ n % b) % b :=
    congrArg (· % b) (Nat.mul_one (a ^ n % b))
  have h_modmod : (a ^ n % b) % b = a ^ n % b := mod_mod (a ^ n) b
  exact h_mod_eq.trans (h_split.trans (h_simp.trans (h_one.trans h_modmod)))

/-- `5^(n + 2) % 6 = 5^n % 6` — the exponent sequence
    `(5^n) mod 6` has period 2 (`5^2 = 25 ≡ 1 mod 6`). -/
private theorem five_pow_add_two_mod_6 (n : Nat) :
    5 ^ (n + 2) % 6 = 5 ^ n % 6 :=
  pow_add_two_mod_pure 5 6 rfl n

/-- Period 2: `configCountD 5 (n + 2) % 7 = configCountD 5 n % 7`.
    The level-up-by-two operation leaves the mod-7 readout
    unchanged.  Holds from `n = 0` (not just eventually). -/
theorem configCountD_5_mod_7_period_2 (n : Nat) :
    configCountD 5 (n + 2) % 7 = configCountD 5 n % 7 := by
  -- LHS = 5^((5^(n+2)) % 6) % 7 by `configCountD_5_mod_7`.
  have h_lhs : configCountD 5 (n + 2) % 7 = 5 ^ ((5 ^ (n + 2)) % 6) % 7 :=
    configCountD_5_mod_7 (n + 2)
  -- RHS = 5^((5^n) % 6) % 7 by `configCountD_5_mod_7`.
  have h_rhs : configCountD 5 n % 7 = 5 ^ ((5 ^ n) % 6) % 7 :=
    configCountD_5_mod_7 n
  -- 5^(n+2) % 6 = 5^n % 6 by `five_pow_add_two_mod_6`.
  have h_exp : 5 ^ (n + 2) % 6 = 5 ^ n % 6 := five_pow_add_two_mod_6 n
  -- Lift to the outer power-7 expression.
  have h_step : 5 ^ ((5 ^ (n + 2)) % 6) % 7 = 5 ^ ((5 ^ n) % 6) % 7 :=
    congrArg (fun x => 5 ^ x % 7) h_exp
  exact h_lhs.trans (h_step.trans h_rhs.symm)

/-- Two-value classification: `configCountD 5 n % 7 ∈ {5, 3}`.
    The first two values determine the entire sequence by
    period 2:
      n = 0  → 5      n = 1  → 3
      n = 2  → 5      n = 3  → 3
      …
    Stated as a closed-form lookup: even `n` yields 5,
    odd `n` yields 3. -/
theorem configCountD_5_mod_7_table : ∀ n : Nat,
    configCountD 5 (2 * n) % 7 = 5
    ∧ configCountD 5 (2 * n + 1) % 7 = 3
  | 0     => by
      refine ⟨?_, ?_⟩
      · show configCountD 5 0 % 7 = 5; decide
      · show configCountD 5 1 % 7 = 3; decide
  | k + 1 => by
      -- 2 * (k+1) = 2*k + 2, so configCountD 5 (2*(k+1)) = configCountD 5 (2*k + 2)
      -- which equals configCountD 5 (2*k) by `configCountD_5_mod_7_period_2`.
      refine ⟨?_, ?_⟩
      · have ih : configCountD 5 (2 * k) % 7 = 5 :=
          (configCountD_5_mod_7_table k).1
        have h_per : configCountD 5 (2 * k + 2) % 7
                    = configCountD 5 (2 * k) % 7 :=
          configCountD_5_mod_7_period_2 (2 * k)
        show configCountD 5 (2 * k + 2) % 7 = 5
        exact h_per.trans ih
      · have ih : configCountD 5 (2 * k + 1) % 7 = 3 :=
          (configCountD_5_mod_7_table k).2
        have h_per : configCountD 5 (2 * k + 1 + 2) % 7
                    = configCountD 5 (2 * k + 1) % 7 :=
          configCountD_5_mod_7_period_2 (2 * k + 1)
        show configCountD 5 (2 * k + 3) % 7 = 3
        exact h_per.trans ih

/-! ## Parametric reduction at `(d, p) = (5, 3)`

`universal_flt_main` requires `a < p`, which fails for `a = 5,
p = 3`.  But the value `5^2 % 3 = 25 % 3 = 1 % 3` reduces by
direct kernel computation, so we obtain the FLT hypothesis via
`decide` and feed it into `configCountD_mod_pure` unchanged.
Mirrors the `(5, 7)` and `(5, 13)` story: `p − 1 = 2` and the
exponent sequence `(5^n) mod 2 = 1` is constant (all `5^n` are
odd).  Hence `configCountD 5 n % 3 = 5^1 % 3 = 2` for every `n`. -/

/-- FLT at `(a, p) = (5, 3)`: `5^2 % 3 = 1 % 3`.  Closed numerals,
    closed by `decide`. -/
theorem flt_5_3 : (5 ^ 2) % 3 = 1 % 3 := by decide

/-- Parametric in `n`: `configCountD 5 n % 3 = 5 ^ ((5^n) % 2) % 3`. -/
theorem configCountD_5_mod_3_param (n : Nat) :
    configCountD 5 n % 3 = 5 ^ ((5 ^ n) % 2) % 3 :=
  configCountD_mod_pure 5 3 flt_5_3 n

/-- Closed form: `configCountD 5 n % 3 = 2` for every `n`.
    Combines the parametric reduction with `5^n % 2 = 1`
    (all `5^n` are odd, since 5 is odd). -/
theorem configCountD_5_mod_3 (n : Nat) : configCountD 5 n % 3 = 2 := by
  have h_param : configCountD 5 n % 3 = 5 ^ ((5 ^ n) % 2) % 3 :=
    configCountD_5_mod_3_param n
  have h_odd : (5 : Nat) ^ n % 2 = 1 :=
    pow_mod_one_pow_pure 5 2 rfl n
  have h_step : 5 ^ ((5 ^ n) % 2) % 3 = 5 ^ 1 % 3 :=
    congrArg (fun x => 5 ^ x % 3) h_odd
  have h_final : (5 : Nat) ^ 1 % 3 = 2 := rfl
  exact (h_param.trans h_step).trans h_final

/-! ## FLT-instantiated parametric reduction at `(d, p) = (5, 11)`

For `p = 11`, `gcd(5, p − 1 = 10) = 5 ≠ 1`, so the exponent
sequence `(5^n) mod 10` is eventually constant (not periodic with
period coprime-to-5).  Still, FLT applies (`gcd(5, 11) = 1`) and
the parametric reduction holds. -/

/-- FLT at `(a, p) = (5, 11)`: `5^10 % 11 = 1 % 11`. -/
theorem flt_5_11 : (5 ^ 10) % 11 = 1 % 11 :=
  E213.Lib.Math.ModArith.UniversalFLT.universal_flt_main
    5 11 (by decide) (by decide) (by decide)
    E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_11

/-- Parametric in `n`: `configCountD 5 n % 11 = 5 ^ ((5^n) % 10) % 11`. -/
theorem configCountD_5_mod_11 (n : Nat) :
    configCountD 5 n % 11 = 5 ^ ((5 ^ n) % 10) % 11 :=
  configCountD_mod_pure 5 11 flt_5_11 n

/-! ## FLT-instantiated parametric reduction at `(d, p) = (5, 13)`

For `p = 13`, `p − 1 = 12`, and `5^2 = 25 ≡ 1 (mod 12)`, so the
multiplicative order of 5 modulo 12 is 2 — same period-2
structure as `(5, 7)`. -/

/-- Prime-gcd witness at `p = 13`.  Mirrors the per-`m` case
    analysis in `Lib/Math/ModArith/UniversalFLT.prime_gcd_*`. -/
private theorem prime_gcd_13 :
    ∀ m, 0 < m → m < 13 →
      (E213.Lib.Math.ModArith.ModBezout.modBezout m 13).1 = 1 := by
  intro m hm hmlt
  match m with
  | 0      => exact absurd hm (Nat.lt_irrefl 0)
  | 1      => decide
  | 2      => decide
  | 3      => decide
  | 4      => decide
  | 5      => decide
  | 6      => decide
  | 7      => decide
  | 8      => decide
  | 9      => decide
  | 10     => decide
  | 11     => decide
  | 12     => decide
  | n + 13 => exact absurd hmlt (Nat.not_lt_of_le (Nat.le_add_left 13 n))

/-- FLT at `(a, p) = (5, 13)`: `5^12 % 13 = 1 % 13`. -/
theorem flt_5_13 : (5 ^ 12) % 13 = 1 % 13 :=
  E213.Lib.Math.ModArith.UniversalFLT.universal_flt_main
    5 13 (by decide) (by decide) (by decide) prime_gcd_13

/-- Parametric in `n`: `configCountD 5 n % 13 = 5 ^ ((5^n) % 12) % 13`. -/
theorem configCountD_5_mod_13 (n : Nat) :
    configCountD 5 n % 13 = 5 ^ ((5 ^ n) % 12) % 13 :=
  configCountD_mod_pure 5 13 flt_5_13 n

/-- `5^(n + 2) % 12 = 5^n % 12` — multiplicative order of 5 mod 12
    is 2 (`5^2 = 25 ≡ 1 mod 12`). -/
private theorem five_pow_add_two_mod_12 (n : Nat) :
    5 ^ (n + 2) % 12 = 5 ^ n % 12 :=
  pow_add_two_mod_pure 5 12 rfl n

/-- Period 2 at `(d, p) = (5, 13)`:
    `configCountD 5 (n + 2) % 13 = configCountD 5 n % 13`. -/
theorem configCountD_5_mod_13_period_2 (n : Nat) :
    configCountD 5 (n + 2) % 13 = configCountD 5 n % 13 := by
  have h_lhs : configCountD 5 (n + 2) % 13 = 5 ^ ((5 ^ (n + 2)) % 12) % 13 :=
    configCountD_5_mod_13 (n + 2)
  have h_rhs : configCountD 5 n % 13 = 5 ^ ((5 ^ n) % 12) % 13 :=
    configCountD_5_mod_13 n
  have h_exp : 5 ^ (n + 2) % 12 = 5 ^ n % 12 := five_pow_add_two_mod_12 n
  have h_step : 5 ^ ((5 ^ (n + 2)) % 12) % 13 = 5 ^ ((5 ^ n) % 12) % 13 :=
    congrArg (fun x => 5 ^ x % 13) h_exp
  exact h_lhs.trans (h_step.trans h_rhs.symm)

/-! ## Parametric reductions at trivial primes `(p ∈ {2, 5})`

Two structural readings of `configCountD 5 n` modulo small primes
where the answer is constant in `n`. -/

/-- `configCountD 5 n % 2 = 1` for all `n`.  Since `5 ≡ 1 (mod 2)`,
    the entire family is odd.  Proof: apply `pow_mod_one_pow_pure`
    with `b = 5, p = 2`. -/
theorem configCountD_5_mod_2 (n : Nat) : configCountD 5 n % 2 = 1 := by
  show (5 : Nat) ^ (5 ^ n) % 2 = 1
  exact pow_mod_one_pow_pure 5 2 rfl (5 ^ n)

/-- `configCountD 5 n % 5 = 0` for all `n`.  Since `5^n ≥ 1` for
    `n ≥ 0`, the count is a positive power of 5, hence divisible
    by 5.  Proof: structural recursion on `n` via the clean
    recursion `configCountD_succ`. -/
theorem configCountD_5_mod_5 :
    ∀ n : Nat, configCountD 5 n % 5 = 0
  | 0     => by show 5 % 5 = 0; decide
  | k + 1 => by
      have h_succ : configCountD 5 (k + 1) = (configCountD 5 k) ^ 5 :=
        E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCountD_succ 5 k
      have ih : configCountD 5 k % 5 = 0 := configCountD_5_mod_5 k
      -- `(b^5) % 5 = ((b^4) * b) % 5` by definition.
      have h_pow : ((configCountD 5 k) ^ 5) % 5
                 = ((configCountD 5 k) ^ 4 * (configCountD 5 k)) % 5 := rfl
      have h_split :
          ((configCountD 5 k) ^ 4 * (configCountD 5 k)) % 5
          = (((configCountD 5 k) ^ 4 % 5) * (configCountD 5 k % 5)) % 5 :=
        mul_mod_pure ((configCountD 5 k) ^ 4) (configCountD 5 k) 5
      have h_simp :
          (((configCountD 5 k) ^ 4 % 5) * (configCountD 5 k % 5)) % 5
          = (((configCountD 5 k) ^ 4 % 5) * 0) % 5 :=
        congrArg (· % 5) (congrArg (((configCountD 5 k) ^ 4 % 5) * ·) ih)
      have h_zero : (((configCountD 5 k) ^ 4 % 5) * 0) % 5 = 0 :=
        congrArg (· % 5) (Nat.mul_zero ((configCountD 5 k) ^ 4 % 5))
      have h_chain : (configCountD 5 k) ^ 5 % 5 = 0 :=
        h_pow.trans (h_split.trans (h_simp.trans h_zero))
      exact (congrArg (· % 5) h_succ).trans h_chain

/-! ## ★★★ Modular-structure capstone at the physics base `d = 5`

Bundles the per-prime parametric results into a single statement
on the `(d, n) = (5, n)` slice of the family.  The constant-`n`
readouts (`p ∈ {2, 3, 5}`) hold parametrically; the period-2
readouts (`p ∈ {7, 13}`) hold for every starting `n`.  Together
they characterise the full mod-{2, 3, 5, 7, 13} fingerprint of
the `N_U` family at the physics base. -/

theorem configCountD_5_modular_structure (n : Nat) :
    -- Trivially constant moduli
    configCountD 5 n % 2 = 1
    ∧ configCountD 5 n % 3 = 2
    ∧ configCountD 5 n % 5 = 0
    -- Period-2 moduli (multiplicative order of 5 mod (p - 1) = 2)
    ∧ configCountD 5 (n + 2) % 7 = configCountD 5 n % 7
    ∧ configCountD 5 (n + 2) % 13 = configCountD 5 n % 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact configCountD_5_mod_2 n
  · exact configCountD_5_mod_3 n
  · exact configCountD_5_mod_5 n
  · exact configCountD_5_mod_7_period_2 n
  · exact configCountD_5_mod_13_period_2 n

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

/-! ## §H Extended modular fingerprint — primes 17, 23, 31, 41

Extends the catalogue `{2, 3, 5, 7, 11, 13}` to the next prime
layer.  Empirical periods:

  · `p = 17`: period 4 in `n` (from `ord_17(5) = 16`, `5^4 ≡ 1 mod 16`)
  · `p = 23`: period 5 (`ord_23(5) = 22`, `5^5 ≡ 1 mod 22`)
  · `p = 31`: period 2 (`ord_31(5) = 3`, parallel to mod-7 / mod-13)
  · `p = 41`: **constant** `9` from `n ≥ 1`
    (`ord_41(5) = 20`, `5^n mod 20 = 5` for `n ≥ 1`,
    hence `5^(5^n) ≡ 5^5 ≡ 9 (mod 41)`)

The period-2 dominance observed at `{7, 11, 13}` does *not* extend
universally: `p = 41` produces a constant, `p = 17, 23` produce
longer periods.  The constant readout at `p = 41` is structurally
distinguished — `41` is the `α_GUT` integer (catalogue), and the
fixed value `9 = NS²` is a count-Lens 2-power.  The modular
fingerprint at `α_GUT` is invariant under fractal level iteration.
-/

/-- Power-mod-base reduction: `a^k % p = (a % p)^k % p`.  Used to
    swap inside the outer power when the inductive hypothesis
    fixes the base mod p.  Standalone induction on the exponent. -/
private theorem pow_mod_base (a p : Nat) :
    ∀ k, a^k % p = (a % p)^k % p
  | 0     => rfl
  | k + 1 => by
      show (a^k * a) % p = ((a % p)^k * (a % p)) % p
      have ih : a^k % p = (a % p)^k % p := pow_mod_base a p k
      calc (a^k * a) % p
          = (a^k % p * (a % p)) % p := mul_mod_pure (a^k) a p
        _ = ((a % p)^k % p * (a % p)) % p := by rw [ih]
        _ = ((a % p)^k * (a % p)) % p :=
              (mul_mod_left_pure ((a % p)^k) (a % p) p).symm

/-! ### §H.1 `p = 41` — constant readout `9` -/

/-- Seed: `5^5 ≡ 9 (mod 41)`.  `3125 = 76·41 + 9`. -/
private theorem five_pow_5_mod_41 : 5^5 % 41 = 9 := by decide

/-- Inductive seed: `9^5 ≡ 9 (mod 41)`.  `59049 = 1440·41 + 9` —
    so `9` is a `5`-power fixed point modulo `41`. -/
private theorem nine_pow_5_mod_41 : 9^5 % 41 = 9 := by decide

/-- ★ **`configCountD 5 (m+1) % 41 = 9` for all `m`**.
    The mod-41 fingerprint is constant across every fractal level
    `n ≥ 1`.  Same proof structure as the Aurifeuillean parametric
    `5^(5^n) ≡ −1 (mod 521)`: induct on `m`, propagate the seed
    via `pow_mul_pure` + `pow_mod_base`, close with the
    self-stabilising identity `9^5 ≡ 9 (mod 41)`. -/
theorem configCountD_5_succ_mod_41 :
    ∀ m, 5^(5^(m+1)) % 41 = 9
  | 0     => five_pow_5_mod_41
  | m + 1 => by
      have ih : 5^(5^(m+1)) % 41 = 9 :=
        configCountD_5_succ_mod_41 m
      have h_pow : 5^(5^(m+1) * 5) = (5^(5^(m+1)))^5 :=
        pow_mul_pure 5 (5^(m+1)) 5
      show 5^(5^(m+2)) % 41 = 9
      rw [show 5^(m+2) = 5^(m+1) * 5 from rfl, h_pow,
          pow_mod_base (5^(5^(m+1))) 41 5, ih]
      -- Goal reduces to `9^5 % 41 = 9`, closed by kernel computation
      -- (the content of `nine_pow_5_mod_41`).

/-- `configCountD 5 1 % 41 = 9` — concrete `n = 1` instance. -/
theorem configCountD_5_1_mod_41 : configCountD 5 1 % 41 = 9 :=
  configCountD_5_succ_mod_41 0

/-- `configCountD 5 2 % 41 = 9` — physics slice (`N_U mod α_GUT`). -/
theorem configCountD_5_2_mod_41 : configCountD 5 2 % 41 = 9 :=
  configCountD_5_succ_mod_41 1

/-- `configCountD 5 3 % 41 = 9` — confirms the constant extends
    beyond the physics slice. -/
theorem configCountD_5_3_mod_41 : configCountD 5 3 % 41 = 9 :=
  configCountD_5_succ_mod_41 2

/-! ### §H.2 Concrete decidable readouts for `p ∈ {17, 23, 31}`

Period structure detected empirically (each verified by `decide`
on small `n`); the corresponding parametric `∀ n` proofs use the
same induction template as `configCountD_5_succ_mod_41` but with
longer-period self-stabilising seeds.  Recorded here as decidable
instances; the parametric proofs are tractable but deferred. -/

/-- `p = 17` table (period 4 from `n = 1`):
    partial cycle through the physics-relevant `n ∈ {0, 1, 2, 3}`. -/
theorem configCountD_5_mod_17_table :
    configCountD 5 0 % 17 = 5
    ∧ configCountD 5 1 % 17 = 14
    ∧ configCountD 5 2 % 17 = 12
    ∧ configCountD 5 3 % 17 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `p = 23` table (period 5 from `n = 1`):
    partial cycle through `n ∈ {0, 1, 2, 3}`. -/
theorem configCountD_5_mod_23_table :
    configCountD 5 0 % 23 = 5
    ∧ configCountD 5 1 % 23 = 20
    ∧ configCountD 5 2 % 23 = 10
    ∧ configCountD 5 3 % 23 = 19 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `p = 31` table (period 2 from `n = 1`, parallel to mod-7 / mod-13):
    full cycle visible in `n ∈ {0, 1, 2, 3}` as `5 → 25 → 5 → 25`. -/
theorem configCountD_5_mod_31_table :
    configCountD 5 0 % 31 = 5
    ∧ configCountD 5 1 % 31 = 25
    ∧ configCountD 5 2 % 31 = 5
    ∧ configCountD 5 3 % 31 = 25 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

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

/-- Extended capstone — modular table at the physics slice `n = 2`
    across the prime set `{17, 23, 31, 41}`.  The `mod 41` entry is
    structurally distinguished: `41 = α_GUT integer`, and the
    constant `9` extends to every `n ≥ 1` (cf.
    `configCountD_5_succ_mod_41`). -/
theorem configCountD_5_2_mod_table_extended :
    configCountD 5 2 % 17 = 12
    ∧ configCountD 5 2 % 23 = 10
    ∧ configCountD 5 2 % 31 = 5
    ∧ configCountD 5 2 % 41 = 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Fractal.ConfigCountModular
