import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.ModArith.UniversalFLT

/-!
# MarkovPrimeFactor — `x² ≡ −1 (mod p)` is unsolvable for `p ≡ 3 (mod 4)`

The Markov uniqueness arc (`Real213/MarkovUniqueness`) showed every Markov number `c` carries a
square root of `−1` mod `c`.  A prime `p ∣ c` then has `x² ≡ −1 (mod p)` solvable.  But this is
**unsolvable when `p ≡ 3 (mod 4)`** — so no prime `≡ 3 (mod 4)` divides a Markov number; every
odd prime factor is `≡ 1 (mod 4)` (Zhang 2007).

This file proves that obstruction *generally* (`MarkovUniqueness` had only finitary `decide`
instances), via the repo's ∅-axiom Fermat little theorem (`universal_flt_main`).  If `x² ≡ −1`
then `x^(p−1) = (x²)^((p−1)/2) ≡ (−1)^((p−1)/2)`; for `p = 4k+3` the exponent `(p−1)/2 = 2k+1`
is odd, so this is `≡ −1`, contradicting Fermat's `x^(p−1) ≡ 1` (forcing `p ∣ 2`).

Self-contained modular pieces first: `(p−1)² ≡ 1` and `(p−1)^(odd) ≡ p−1` mod `p`.
-/

namespace E213.Lib.Math.ModArith.MarkovPrimeFactor

open E213.Tactic.NatHelper (add_mul_mod_self_pure two_mul add_mul mod_mod_pure)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.PureNat (pow_add)

/-- `a^(m·n) = (a^m)^n`.  ∅-axiom (induction on `n`). -/
theorem pow_mul_loc (a m : Nat) : ∀ n, a ^ (m * n) = (a ^ m) ^ n
  | 0 => by rw [Nat.mul_zero]; rfl
  | n + 1 => by rw [Nat.mul_succ, pow_add, pow_mul_loc a m n, Nat.pow_succ]

/-! ## §1 — `(p−1)² ≡ 1 (mod p)`: `−1` squares to `1` -/

/-- ★★★ **`(e+1)² ≡ 1 (mod e+2)`** — i.e. `(p−1)² ≡ 1 (mod p)` for `p = e+2 ≥ 2`.  Writing
    `p = e+2`: `(e+1)² = (e+2)·e + 1`, so the square is `1` mod `p`.  Pure `ℕ`. -/
theorem neg_one_sq_mod (e : Nat) : ((e + 1) * (e + 1)) % (e + 2) = 1 % (e + 2) := by
  have hid : (e + 1) * (e + 1) = (e + 2) * e + 1 := by
    have hL : (e + 1) * (e + 1) = e * e + e + e + 1 := by
      rw [add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
    have hR : (e + 2) * e + 1 = e * e + e + e + 1 := by
      rw [add_mul, two_mul, ← Nat.add_assoc]
    exact hL.trans hR.symm
  rw [hid, Nat.add_comm ((e + 2) * e) 1, Nat.mul_comm (e + 2) e]
  exact add_mul_mod_self_pure 1 (e + 2) e

/-! ## §2 — `(p−1)^(2k+1) ≡ p−1 (mod p)`: odd powers of `−1` -/

/-- ★★★★ **`(e+1)^(2k+1) ≡ e+1 (mod e+2)`** — odd powers of `−1` are `−1`.  Since
    `(e+1)² ≡ 1`, `(e+1)^(2k+1) = (e+1)·((e+1)²)^k ≡ (e+1)·1`. -/
theorem neg_one_odd_pow_mod (e k : Nat) :
    ((e + 1) ^ (2 * k + 1)) % (e + 2) = (e + 1) % (e + 2) := by
  -- (e+1)^(2k+1) = (e+1) * ((e+1)*(e+1))^k
  have hfact : (e + 1) ^ (2 * k + 1) = (e + 1) * (((e + 1) * (e + 1)) ^ k) := by
    rw [pow_add, Nat.pow_one, pow_mul_loc (e + 1) 2 k, Nat.pow_two, Nat.mul_comm]
  rw [hfact, mul_mod_pure (e + 1) (((e + 1) * (e + 1)) ^ k) (e + 2)]
  -- ((e+1)*(e+1))^k % (e+2) = (1 % (e+2))^k % (e+2) = 1 % (e+2)
  have hone : (((e + 1) * (e + 1)) ^ k) % (e + 2) = 1 % (e + 2) := by
    rw [pow_mod_base, neg_one_sq_mod, ← pow_mod_base, Nat.one_pow]
  rw [hone]
  -- ((e+1)%(e+2) * (1%(e+2))) % (e+2) = (e+1)%(e+2)
  have h1 : (1 : Nat) % (e + 2) = 1 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 e))
  rw [h1, Nat.mul_one, mod_mod_pure]

/-! ## §3 — `p ∣ (n+1) ⟹ n ≡ p−1 (mod p)`: the residue of a `√(−1)` -/

/-- `(e+2) ∣ (n+1) ⟹ n % (e+2) = e+1` — i.e. `p ∣ n+1 ⟹ n ≡ p−1 (mod p)`.  Writing the
    cofactor `n+1 = (e+2)·(s+1)` gives `n = (e+1) + s·(e+2)`. -/
theorem pred_mod_of_dvd_succ (e n : Nat) (h : (e + 2) ∣ (n + 1)) : n % (e + 2) = e + 1 := by
  obtain ⟨t, ht⟩ := h
  cases t with
  | zero =>
      rw [Nat.mul_zero] at ht
      exact (E213.Tactic.NatHelper.zero_ne_succ_213 n ht.symm).elim
  | succ s =>
    have h1 : n + 1 = ((e + 1) + s * (e + 2)) + 1 := by
      rw [ht, Nat.mul_succ, Nat.mul_comm (e + 2) s, Nat.add_comm (e + 1) (s * (e + 2)),
          Nat.add_assoc]
    have hn : n = (e + 1) + s * (e + 2) := E213.Tactic.NatHelper.add_right_cancel_pure h1
    rw [hn]
    exact (add_mul_mod_self_pure (e + 1) (e + 2) s).trans
      (Nat.mod_eq_of_lt (Nat.lt_succ_self (e + 1)))

/-! ## §4 — the obstruction: `x² ≡ −1 (mod 4k+3)` is impossible -/

open E213.Lib.Math.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.ModArith.ModBezout (modBezout)

/-- ★★★★★ **No square root of `−1` mod `p ≡ 3 (mod 4)`.**  For `p = 4k+3` satisfying the
    prime-gcd hypothesis (the ∅-axiom proxy for primality used by `universal_flt_main`), there
    is no `x` with `p ∣ x²+1`.  Hence no prime `≡ 3 (mod 4)` divides a Markov number.

    Proof: Fermat gives `x^(p−1) ≡ 1`.  But `x^(p−1) = (x²)^(2k+1)` and `x² ≡ −1 = p−1`, so
    `x^(p−1) ≡ (p−1)^(2k+1) ≡ p−1` (odd power of `−1`, `neg_one_odd_pow_mod`).  Thus `p−1 ≡ 1`,
    forcing `p ∣ 2` — impossible for `p = 4k+3 ≥ 3`. -/
theorem no_sqrt_neg_one_4k3 (k x : Nat)
    (hpg : ∀ m, 0 < m → m < 4 * k + 3 → (modBezout m (4 * k + 3)).1 = 1)
    (hx0 : 0 < x) (hxlt : x < 4 * k + 3) :
    ¬ ((4 * k + 3) ∣ (x * x + 1)) := by
  intro hdvd
  have hp1 : 1 < 4 * k + 3 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 3 (4 * k))
  -- Fermat
  have hflt : (x ^ ((4 * k + 3) - 1)) % (4 * k + 3) = 1 % (4 * k + 3) :=
    universal_flt_main x (4 * k + 3) hp1 hx0 hxlt hpg
  -- x² ≡ −1 = 4k+2,  and (4k+2)^(2k+1) ≡ 4k+2
  have hsqmod : (x * x) % (4 * k + 3) = 4 * k + 2 := pred_mod_of_dvd_succ (4 * k + 1) (x * x) hdvd
  have hoddpow : (4 * k + 2) ^ (2 * k + 1) % (4 * k + 3) = 4 * k + 2 :=
    (neg_one_odd_pow_mod (4 * k + 1) k).trans
      (Nat.mod_eq_of_lt (Nat.lt_succ_self (4 * k + 1 + 1)))
  -- evaluate x^(p−1) % p = 4k+2
  have hval : (x ^ ((4 * k + 3) - 1)) % (4 * k + 3) = 4 * k + 2 := by
    have hexp : (4 * k + 3) - 1 = 2 * (2 * k + 1) := by
      rw [show (4 * k + 3) = (4 * k + 2) + 1 from rfl,
          E213.Tactic.NatHelper.add_sub_cancel_right,
          Nat.mul_add, Nat.mul_one, ← E213.Tactic.NatHelper.mul_assoc]
    rw [hexp, pow_mul_loc x 2 (2 * k + 1), Nat.pow_two,
        pow_mod_base (x * x) (4 * k + 3) (2 * k + 1), hsqmod, hoddpow]
  -- contradiction: 4k+2 = 1
  have hbad : 4 * k + 2 = 1 := by
    have := hval.symm.trans hflt
    rwa [Nat.mod_eq_of_lt hp1] at this
  have h2le : 2 ≤ 4 * k + 2 := Nat.le_add_left 2 (4 * k)
  rw [hbad] at h2le
  exact absurd h2le (by decide)

/-! ## §5 — concrete primes `≡ 3 (mod 4)` (general theorem, not `decide`) -/

/-- `x² ≡ −1 (mod 7)` is impossible (`7 = 4·1+3`), from the general `no_sqrt_neg_one_4k3` with
    the repo's per-prime gcd witness `prime_gcd_7`. -/
theorem no_sqrt_neg_one_mod_7 (x : Nat) (hx0 : 0 < x) (hxlt : x < 7) :
    ¬ ((7 : Nat) ∣ (x * x + 1)) :=
  no_sqrt_neg_one_4k3 1 x E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_7 hx0 hxlt

/-- `x² ≡ −1 (mod 11)` is impossible (`11 = 4·2+3`), via `prime_gcd_11`. -/
theorem no_sqrt_neg_one_mod_11 (x : Nat) (hx0 : 0 < x) (hxlt : x < 11) :
    ¬ ((11 : Nat) ∣ (x * x + 1)) :=
  no_sqrt_neg_one_4k3 2 x E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_11 hx0 hxlt

end E213.Lib.Math.ModArith.MarkovPrimeFactor
