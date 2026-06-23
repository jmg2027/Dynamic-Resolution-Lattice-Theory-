import E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot
import E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.NatRing213
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Pow213

/-!
# CyclicCharacterOrthogonality — general-order orthogonality **inside `ℤ/p`** (∅-axiom)

the `fourier` decomposition records the orthogonality
target `Σ_x χ(x) = 0` and the residual that *arbitrary*-order roots of unity need
the cyclotomic ring `ℤ[ζ_n]`.  The order-2 leg was cashed via the `(−1)^k`
parity telescope (`CharacterOrthogonality.quadratic_orthogonality`); orders
`3, 6` (and `4` Gaussian) via concrete roots of unity in `ℤ[ω]` / `ℤ[i]`
(`RootOfUnityOrthogonality`, `GaussianOrthogonality`).  That cyclotomic-ring
route only reaches the orders `{1,2,3,4,6}` realised by Eisenstein/Gaussian
integers.

This module closes the **general-order** orthogonality in the *finite-field*
direction, **with no cyclotomic ring**.  A nontrivial multiplicative character
mod a prime `p` sums to `0` for *any* order `n ∣ p−1`: a primitive root `g`
gives an element

>   `ω := g^{(p−1)/n} mod p`

of multiplicative order exactly `n`, and `Σ_{k<n} ω^k ≡ 0 (mod p)` follows from
the **same geometric telescope** that powers the cyclotomic case — `ω` is a
genuine `n`-th root of unity *inside `ℤ/p`*, no `ζ_n` adjoined.

## The engine — the geometric telescope over `ℕ` (subtraction-free)

The single algebraic identity (`geomNat_telescope`, generic over `ℕ`):

>   `ω · Σ_{k<n} ω^k + 1 = Σ_{k<n} ω^k + ω^n`.

This is the order-`n` generalisation of the order-2 `+1,−1` pair-cancellation,
written without `ℕ`-subtraction.  Reduced mod `p` with `ω^n ≡ 1`, it gives
`ω·S + 1 ≡ S + 1`, i.e. `p ∣ (ω−1)·S`; Euclid (`nat_prime_dvd_mul`) and `ω ≢ 1`
force `p ∣ S`, i.e. `Σ ≡ 0`.

  * ★★★ `geomNat_telescope`        — `ω·S + 1 = S + ω^n` over `ℕ`.
  * ★★★★ `cyclic_orthogonality_modp` — for a primitive root `g` and `n ∣ p−1`,
    `1 < n`, the order-`n` character sum `Σ_{k<n} (g^{(p−1)/n})^k ≡ 0 (mod p)`.
  * ★★★ `omega_order_n`            — `ω = g^{(p−1)/n} mod p` is an `n`-th root of
    unity (`ω^n ≡ 1`) and is nontrivial (`ω ≢ 1`).
  * ★★★ `order5_mod11_orthogonality` — concrete prime-order instance:
    `Σ_{k<5} 4^k ≡ 0 (mod 11)` (`ω = 2² = 4` of order `5`, `2` primitive mod `11`).

All ∅-axiom (`#print axioms` clean).

## How far the finite-field direction reaches

The cyclotomic-ℤ route caps at `{1,2,3,4,6}` (the only `n` with a primitive
`n`-th root of unity that is an Eisenstein/Gaussian integer).  This route reaches
**every** order `n ∣ p−1` for **every** prime `p` — in particular *prime* orders
like `5` (mod `11`), `7` (mod `29`), … that the cyclotomic-ℤ side never touches.
The residual: the character here is the *additive-exponent* / multiplicative
character `g^k ↦ ω^k` valued **in `ℤ/p`**, not a `ℂ`-valued / `ℤ[ζ_n]`-valued
character; bridging the two valuations (a ring map `ℤ[ζ_n] → ℤ/p` sending `ζ_n ↦
ω`) is the remaining cyclotomic-vs-finite-field reconciliation, untouched here.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CyclicCharacterOrthogonality

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP pow_ord ord_dvd)
open E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot (exists_primitive_root)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (not_dvd_pow)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul dvd_of_mod_zero mod_zero_of_dvd)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Meta.Nat.MulMod213 (mul_mod_pure mul_mod_left_pure)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.AddMod213 (add_mod_gen)
open E213.Tactic.NatHelper (mul_sub add_sub_add_right sub_pos_of_lt)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_right)
open E213.Meta.Nat.AddMod213 (mod_mod)
open E213.Lib.Math.NumberTheory.PerfectNumbers (prime_of_bounded)

/-! ## §1 — the geometric sum over `ℕ` and the subtraction-free telescope -/

/-- The partial geometric sum `Σ_{k=0}^{n−1} ω^k` over `ℕ`. -/
def geomNat (w : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => geomNat w n + w ^ n

@[simp] theorem geomNat_zero (w : Nat) : geomNat w 0 = 0 := rfl
theorem geomNat_succ (w n : Nat) : geomNat w (n + 1) = geomNat w n + w ^ n := rfl

/-- ★★★ **The geometric telescope over `ℕ`** (subtraction-free):

      `ω · Σ_{k<n} ω^k + 1 = Σ_{k<n} ω^k + ω^n`.

    The order-`n` generalisation of `1 + (−1) = 0`.  Proof by induction on `n`:
    the step multiplies through and the `ω·ω^n` term advances the geometric
    sum by one while the running `+ ω^n` collapses. -/
theorem geomNat_telescope (w : Nat) :
    ∀ n, w * geomNat w n + 1 = geomNat w n + w ^ n
  | 0     => by
    show w * 0 + 1 = 0 + 1
    rw [Nat.mul_zero]
  | n + 1 => by
    -- IH: w * S n + 1 = S n + w^n
    have ih := geomNat_telescope w n
    show w * (geomNat w n + w ^ n) + 1 = (geomNat w n + w ^ n) + w ^ (n + 1)
    rw [Nat.mul_add]
    -- w * S n + w * w^n + 1 = S n + w^n + w^(n+1)
    -- regroup LHS as (w * S n + 1) + w * w^n  then apply IH
    rw [Nat.add_right_comm (w * geomNat w n) (w * w ^ n) 1, ih]
    -- (S n + w^n) + w * w^n = (S n + w^n) + w^(n+1)
    have hpow : w * w ^ n = w ^ (n + 1) := by
      rw [pow_add_pure w n 1, Nat.pow_one, Nat.mul_comm]
    rw [hpow]

/-! ## §2 — `ω = g^{(p−1)/n}` is an `n`-th root of unity of order `n` -/

/-- For a primitive root `g` and `n ∣ p−1` with `1 < n`, the element
    `ω = g^{(p−1)/n} mod p` is a nontrivial `n`-th root of unity in `ℤ/p`:

      `ω^n ≡ 1 (mod p)`   and   `ω ≢ 1 (mod p)`,

    hence (with `ω < p`) `ω ≠ 1` as a `ℕ`-residue and `ω ≥ 1`.

    `ω^n ≡ 1`: `(g^{(p−1)/n})^n = g^{(p−1)/n · n} = g^{p−1} ≡ 1`.
    `ω ≢ 1`: else `g^{(p−1)/n} ≡ 1` ⟹ `(p−1) ∣ (p−1)/n` (order of `g` is `p−1`),
    impossible since `0 < (p−1)/n < p−1` (uses `1 < n ≤ p−1`). -/
theorem omega_order_n (p g n : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg1 : 1 ≤ g) (hgle : g ≤ p - 1) (hord : ordModP g p = p - 1)
    (hn1 : 1 < n) (hndvd : n ∣ (p - 1)) :
    (g ^ ((p - 1) / n) % p) ^ n % p = 1 ∧ (g ^ ((p - 1) / n) % p) ≠ 1 ∧
      1 ≤ (g ^ ((p - 1) / n) % p) ∧ (g ^ ((p - 1) / n) % p) < p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  have hg0 : 0 < g := hg1
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hn1)
  -- the divisibility equation: p - 1 = n * q
  obtain ⟨q, hq⟩ := hndvd          -- p - 1 = n * q
  have hp1pos : 0 < p - 1 := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · exfalso
      rw [h0, Nat.mul_zero] at hq
      -- p - 1 = 0, but p > 1 gives p - 1 ≥ 1
      exact absurd hq (Nat.not_eq_zero_of_lt (sub_pos_of_lt hp))
    · rw [hq]; exact Nat.mul_pos hn0 hpos
  have hdivn : (p - 1) / n = q := by
    rw [hq, mul_div_cancel_left_pure n q hn0]
  -- q ≥ 1 and q < p-1
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hq; exact Nat.lt_irrefl 0 (hq ▸ hp1pos)
    · exact hpos
  have hqlt : q < p - 1 := by
    rw [hq]
    -- q < n * q  since 1 < n and q ≥ 1
    calc q = 1 * q := (Nat.one_mul q).symm
      _ < n * q := nat_mul_lt_mul_right (Nat.lt_of_lt_of_le Nat.zero_lt_one hq1) hn1
  -- coprimality bits: p ∤ g, p ∤ g^e
  have hnpg : ¬ p ∣ g := fun hd =>
    absurd (le_of_dvd_pos p g hg0 hd) (Nat.not_le.mpr hglt)
  refine ⟨?_, ?_, ?_, Nat.mod_lt _ hppos⟩
  · -- ω^n ≡ 1
    -- ω^n % p = (g^e % p)^n % p = (g^e)^n % p = g^(e*n) % p = g^(p-1) % p = 1
    rw [← pow_mod_base (g ^ ((p - 1) / n)) p n, ← pow_mul_loc g ((p - 1) / n) n]
    rw [hdivn]
    -- g^(q*n) % p ; q*n = p-1
    have heqn : q * n = p - 1 := by rw [hq, Nat.mul_comm]
    rw [heqn]
    -- goal: g ^ (p - 1) % p = 1
    have hpow1 : g ^ (p - 1) % p = 1 := by
      have h := pow_ord g p hp hpr hg0 hglt
      rwa [hord] at h
    exact hpow1
  · -- ω ≠ 1
    intro hw1
    -- g^e % p = 1, so ord g ∣ e, i.e. (p-1) ∣ q
    have hdvd : ordModP g p ∣ ((p - 1) / n) :=
      ord_dvd g p hp hpr hg0 hglt _ hw1
    rw [hord, hdivn] at hdvd
    -- (p-1) ∣ q with 0 < q < p-1
    exact absurd (le_of_dvd_pos (p - 1) q hq1 hdvd) (Nat.not_le.mpr hqlt)
  · -- 1 ≤ ω
    have hnp_pow : ¬ p ∣ g ^ ((p - 1) / n) :=
      not_dvd_pow g p ((p - 1) / n) hp hpr hnpg
    exact Nat.pos_of_ne_zero (fun h0 => hnp_pow (dvd_of_mod_zero _ p h0))

/-! ## §3 — general-order orthogonality in `ℤ/p` -/

/-- `(a + b) % p = (a + b % p) % p` — reduce the second summand mod `p`. -/
theorem add_right_mod (a b p : Nat) : (a + b) % p = (a + b % p) % p := by
  rw [add_mod_gen a b p, add_mod_gen a (b % p) p, mod_mod]

/-- ★★★ **The mod-`p` telescope step.**  If `ω^n ≡ 1 (mod p)` then
    `ω · S + 1 ≡ S + 1 (mod p)` where `S = Σ_{k<n} ω^k`.  Immediate from
    `geomNat_telescope` (`ω·S + 1 = S + ω^n`) and `ω^n ≡ 1`. -/
theorem telescope_mod (w p n : Nat) (hwn : w ^ n % p = 1) :
    (w * geomNat w n + 1) % p = (geomNat w n + 1) % p := by
  rw [geomNat_telescope w n]
  -- (S + w^n) % p = (S + 1) % p ; reduce the second summand mod p on both sides
  rw [add_right_mod (geomNat w n) (w ^ n) p, hwn]

/-- ★★★★ **General-order character orthogonality inside `ℤ/p`.**

    For a prime `p`, a primitive root `g`, and any order `n ∣ p−1` with `1 < n`,
    the order-`n` multiplicative character summed over its full period vanishes
    mod `p`:

      `Σ_{k=0}^{n−1} ω^k ≡ 0 (mod p)`,   `ω = g^{(p−1)/n} mod p`.

    `ω` is a genuine primitive `n`-th root of unity *in `ℤ/p`* (`omega_order_n`).
    The geometric telescope gives `p ∣ (ω−1)·S`; Euclid + `ω ≢ 1` (so `ω−1 ≠ 0`
    and `ω−1 < p`) force `p ∣ S`.  This is the order-`n` analogue of
    `quadratic_orthogonality`, with **no cyclotomic ring** — `ω` lives in the
    prime field itself. -/
theorem cyclic_orthogonality_of_root (p w n : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hwn : w ^ n % p = 1) (hwne : w ≠ 1) (hw1 : 1 ≤ w) (hwlt : w < p) :
    geomNat w n % p = 0 := by
  -- telescope mod p:  w*S + 1 ≡ S + 1
  have htel : (w * geomNat w n + 1) % p = (geomNat w n + 1) % p :=
    telescope_mod w p n hwn
  -- so  p ∣ (w*S + 1) − (S + 1) = w*S − S = (w−1)*S
  have hge : geomNat w n + 1 ≤ w * geomNat w n + 1 :=
    Nat.add_le_add_right (Nat.le_mul_of_pos_left (geomNat w n) hw1) 1
  have hdvd1 : p ∣ ((w * geomNat w n + 1) - (geomNat w n + 1)) :=
    mod_eq_dvd_sub _ _ p (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) hge htel
  -- simplify the difference to (w − 1) * S
  have hsubeq : (w * geomNat w n + 1) - (geomNat w n + 1) = (w - 1) * geomNat w n := by
    rw [add_sub_add_right (w * geomNat w n) 1 (geomNat w n)]
    -- w * S - S = (w - 1) * S
    rw [Nat.mul_comm (w - 1) (geomNat w n), mul_sub (geomNat w n) w 1,
        Nat.mul_one, Nat.mul_comm (geomNat w n) w]
  rw [hsubeq] at hdvd1
  -- Euclid: p ∣ (w−1) ∨ p ∣ S
  rcases nat_prime_dvd_mul p hp hpr (w - 1) (geomNat w n) hdvd1 with hdw | hdS
  · -- p ∣ (w − 1) with 0 < w − 1 < p ⟹ w − 1 = 0 ⟹ w = 1, contradiction
    exfalso
    have hwm1_pos : 0 < w - 1 := by
      rcases Nat.eq_zero_or_pos (w - 1) with h0 | hpos
      · exact absurd (Nat.le_antisymm (Nat.le_of_sub_eq_zero h0) hw1) hwne
      · exact hpos
    have hwm1_lt : w - 1 < p := Nat.lt_of_le_of_lt (Nat.sub_le w 1) hwlt
    exact absurd (le_of_dvd_pos p (w - 1) hwm1_pos hdw) (Nat.not_le.mpr hwm1_lt)
  · exact mod_zero_of_dvd _ p hdS

theorem cyclic_orthogonality_modp (p g n : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg1 : 1 ≤ g) (hgle : g ≤ p - 1) (hord : ordModP g p = p - 1)
    (hn1 : 1 < n) (hndvd : n ∣ (p - 1)) :
    geomNat (g ^ ((p - 1) / n) % p) n % p = 0 := by
  obtain ⟨hwn, hwne, hw1, hwlt⟩ := omega_order_n p g n hp hpr hg1 hgle hord hn1 hndvd
  exact cyclic_orthogonality_of_root p (g ^ ((p - 1) / n) % p) n hp hpr hwn hwne hw1 hwlt

/-- **Fully internal form.**  For a prime `p` and any order `n ∣ p−1` with
    `1 < n`, a primitive root `g` exists (`exists_primitive_root`) and the
    order-`n` character sum `Σ_{k<n} (g^{(p−1)/n})^k ≡ 0 (mod p)` — general-order
    orthogonality with the primitive root produced internally. -/
theorem cyclic_orthogonality_exists (p n : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hn1 : 1 < n) (hndvd : n ∣ (p - 1)) :
    ∃ g, (1 ≤ g ∧ g ≤ p - 1 ∧ ordModP g p = p - 1) ∧
      geomNat (g ^ ((p - 1) / n) % p) n % p = 0 := by
  obtain ⟨g, hg1, hgle, hord⟩ := exists_primitive_root p hp hpr
  exact ⟨g, ⟨hg1, hgle, hord⟩,
    cyclic_orthogonality_modp p g n hp hpr hg1 hgle hord hn1 hndvd⟩

/-! ## §4 — concrete prime-order instance (order 5 mod 11)

`2` is a primitive root mod `11`; `ω = 2² = 4` has multiplicative order `5`
(`5 ∣ 10`).  Order `5` is a *prime* order the cyclotomic-ℤ route never reaches —
this is the first prime-order orthogonality past `{2,3}` cashed concretely. -/

/-- `11` is prime: `∀ d, d ∣ 11 → d = 1 ∨ d = 11` (bounded check). -/
theorem prime11_hpr : ∀ d, d ∣ 11 → d = 1 ∨ d = 11 :=
  (prime_of_bounded (by decide) (B := 4) (by decide) (by decide)).2

/-- `2` is a primitive root mod `11`: `ordModP 2 11 = 10`. -/
theorem two_primitive_mod11 : ordModP 2 11 = 10 := by decide

/-- `ω = 4 = 2² mod 11` is a primitive 5th root of unity in `ℤ/11`:
    `4^5 ≡ 1 (mod 11)` and `4 ≢ 1`. -/
theorem four_order5_mod11 : 4 ^ 5 % 11 = 1 ∧ (4 : Nat) ≠ 1 := by decide

/-- The order-5 geometric sum `Σ_{k<5} 4^k = 1+4+16+64+256 = 341 = 31·11` reduces
    to `0` mod `11`. -/
theorem geomNat_four_five : geomNat 4 5 = 341 := by decide

/-- ★★★ **Concrete prime-order orthogonality `Σ_{k<5} 4^k ≡ 0 (mod 11)`.**
    The order-5 character sum vanishes — a prime order beyond the cyclotomic-ℤ
    route's `{2,3,4,6}`, realised entirely inside `ℤ/11` with `ω = 4`. -/
theorem order5_mod11_orthogonality : geomNat 4 5 % 11 = 0 := by decide

/-- The same instance via the general theorem: with `p = 11`, `g = 2`, `n = 5`,
    `(p−1)/n = 2` and `g^2 % p = 4`, so `cyclic_orthogonality_modp` specialises to
    `Σ_{k<5} 4^k ≡ 0 (mod 11)`.  Confirms the general engine reproduces the
    concrete `decide`. -/
theorem order5_mod11_via_general : geomNat (2 ^ ((11 - 1) / 5) % 11) 5 % 11 = 0 :=
  cyclic_orthogonality_modp 11 2 5 (by decide) prime11_hpr
    (by decide) (by decide) two_primitive_mod11 (by decide) ⟨2, rfl⟩

end E213.Lib.Math.NumberTheory.ModArith.CyclicCharacterOrthogonality
