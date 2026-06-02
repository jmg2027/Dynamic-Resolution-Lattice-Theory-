import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Gcd213
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

/-! ## §6 — Euclid's lemma and "≤ 2 roots mod a prime"

The other side of the root count: for a *prime* modulus `p`, the congruence `x² ≡ −1 (mod p)`
has at most the two roots `±u`.  This is the input the uniqueness reduction needs at prime
Markov numbers.  It rests on **Euclid's lemma** `p ∣ a·b → p ∣ a ∨ p ∣ b`, which here comes
constructively from the modular inverse (`modBezout`): if `a` is invertible mod `p`
(`(a·a') % p = 1`) and `p ∣ a·b`, then `p ∣ b`. -/

open E213.Meta.Nat.Gcd213 (dvd_sub_213)

/-- `g ∣ m → g ∣ m·k`.  ∅-axiom. -/
theorem dvd_mul_right_loc (g m k : Nat) (h : g ∣ m) : g ∣ (m * k) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s * k, by rw [hs, E213.Tactic.NatHelper.mul_assoc]⟩

/-- ★★★★ **Euclid's lemma via a modular inverse.**  If `(a·a') % p = 1` (so `a'` inverts `a`
    mod `p`) and `p ∣ a·b`, then `p ∣ b`.  Multiply `p ∣ a·b` by `a'`: `b·(a·a') = b + p·(b·q)`
    with `a·a' = p·q + 1`, so `p ∣ b·(a·a') − p·(b·q) = b`. -/
theorem euclid_via_inverse (p a b a' : Nat) (hinv : (a * a') % p = 1)
    (hdvd : p ∣ (a * b)) : p ∣ b := by
  -- a·a' = p·q + 1  (q abstract, to avoid rewriting inside the quotient)
  obtain ⟨q, hq⟩ : ∃ q, a * a' = p * q + 1 := by
    refine ⟨(a * a') / p, ?_⟩
    have hdm := E213.Meta.Nat.AddMod213.div_add_mod (a * a') p
    rw [hinv] at hdm; exact hdm.symm
  -- p ∣ b·(a·a')
  have hdb : p ∣ (b * (a * a')) := by
    have h1 : p ∣ (a * b) * a' := dvd_mul_right_loc p (a * b) a' hdvd
    have he : (a * b) * a' = b * (a * a') := by
      rw [E213.Tactic.NatHelper.mul_assoc a b a', E213.Tactic.NatHelper.mul_left_comm a b a']
    rwa [he] at h1
  -- b·(a·a') = b + p·(b·q)
  have hbq : b * (a * a') = b + p * (b * q) := by
    rw [hq, Nat.mul_add, Nat.mul_one, Nat.add_comm (b * (p * q)) b,
        E213.Tactic.NatHelper.mul_left_comm b p q]
  -- subtract the multiple
  have hle : p * (b * q) ≤ b * (a * a') := hbq ▸ Nat.le_add_left _ _
  have hsub := dvd_sub_213 (p * (b * q)) (b * (a * a')) p hle ⟨b * q, rfl⟩ hdb
  rwa [hbq, E213.Tactic.NatHelper.add_sub_cancel_right] at hsub

/-- `(y+d)² = y² + d·(2y+d)`.  ∅-axiom expansion. -/
theorem sq_expand (y d : Nat) : (y + d) * (y + d) = y * y + d * (2 * y + d) := by
  have hL : (y + d) * (y + d) = y * y + (d * y + (d * y + d * d)) := by
    rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm y d, Nat.add_assoc]
  have hR : y * y + d * (2 * y + d) = y * y + (d * y + (d * y + d * d)) := by
    rw [Nat.mul_add, two_mul, Nat.mul_add, Nat.add_assoc]
  exact hL.trans hR.symm

/-- The only multiple of `p` strictly between `0` and `2p` is `p`. -/
theorem eq_p_of_dvd (p s : Nat) (hp : 1 < p) (h0 : 0 < s) (hlt : s < 2 * p) (hd : p ∣ s) :
    s = p := by
  obtain ⟨t, ht⟩ := hd
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.mul_zero] at ht; rw [ht] at h0; exact absurd h0 (Nat.lt_irrefl 0)
    · exact h
  have ht2 : t < 2 := by
    rcases Nat.lt_or_ge t 2 with h | h
    · exact h
    · exfalso
      have hge : 2 * p ≤ p * t := by rw [Nat.mul_comm 2 p]; exact Nat.mul_le_mul_left p h
      rw [← ht] at hge
      exact Nat.lt_irrefl s (E213.Tactic.NatHelper.lt_of_lt_le hlt hge)
  have : t = 1 := Nat.le_antisymm (Nat.le_of_lt_succ ht2) ht1
  rw [ht, this, Nat.mul_one]

open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.ModArith.ModBezoutInvariant (modBezout_inverse_correct)

/-- Ordered core of the prime two-roots fact: with `x = y+d`, two roots of `x²≡−1` mod a prime
    `p` collapse to `d = 0` (equal) or `(y+d)+y = p` (negatives).  Uses `sq_expand` for the
    difference `(y+d)²−y² = d·(2y+d)`, `euclid_via_inverse` (`d` invertible since `0<d<p`) to
    pass from `p ∣ d·(2y+d)` to `p ∣ (2y+d) = (y+d)+y`, then `eq_p_of_dvd`. -/
theorem two_roots_ordered (p y d : Nat) (hp : 1 < p)
    (hpg : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1)
    (hlt : y + d < p) (hy1 : 1 ≤ y)
    (hxr : ((y + d) * (y + d) + 1) % p = 0) (hyr : (y * y + 1) % p = 0) :
    d = 0 ∨ (y + d) + y = p := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · left; exact hd0
  · right
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
    have hX : p ∣ ((y + d) * (y + d) + 1) := dvd_of_mod_eq_zero hxr
    have hY : p ∣ (y * y + 1) := dvd_of_mod_eq_zero hyr
    -- p ∣ d·(2y+d) = (y+d)²+1 − (y²+1)
    have hdiff : p ∣ (d * (2 * y + d)) := by
      have hle : y * y + 1 ≤ (y + d) * (y + d) + 1 := by
        rw [sq_expand]
        exact Nat.add_le_add_right (Nat.le_add_right (y * y) (d * (2 * y + d))) 1
      have hs := dvd_sub_213 (y * y + 1) ((y + d) * (y + d) + 1) p hle hY hX
      have heq : (y + d) * (y + d) + 1 - (y * y + 1) = d * (2 * y + d) := by
        rw [sq_expand, Nat.add_right_comm (y * y) (d * (2 * y + d)) 1,
            Nat.add_comm (y * y + 1) (d * (2 * y + d)), E213.Tactic.NatHelper.add_sub_cancel_right]
      rwa [heq] at hs
    -- d invertible mod p (0 < d < p)
    have hdlt : d < p := Nat.lt_of_le_of_lt (Nat.le_add_left d y) hlt
    have hinv : (d * (modBezout d p).2) % p = 1 := by
      rw [modBezout_inverse_correct d p hppos (hpg d hdpos hdlt), Nat.mod_eq_of_lt hp]
    -- Euclid ⟹ p ∣ (2y+d) = (y+d)+y
    have h2yd : p ∣ ((y + d) + y) := by
      have := euclid_via_inverse p d (2 * y + d) (modBezout d p).2 hinv hdiff
      rwa [two_mul, Nat.add_right_comm y y d] at this
    -- 0 < (y+d)+y < 2p, p ∣ it ⟹ = p
    have hpos : 0 < (y + d) + y :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hy1 (Nat.le_add_left y (y + d)))
    have hlt2 : (y + d) + y < 2 * p := by
      rw [two_mul]
      exact Nat.add_lt_add hlt (Nat.lt_of_le_of_lt (Nat.le_add_right y d) hlt)
    exact eq_p_of_dvd p ((y + d) + y) hp hpos hlt2 h2yd

/-- ★★★★★ **At most two roots of `x² ≡ −1` mod a prime.**  For a modulus `p` satisfying the
    prime-gcd hypothesis, any two roots `x, y < p` of `x² ≡ −1 (mod p)` satisfy `x = y` or
    `x + y = p` (`= ±` each other).  This is exactly `SqrtNegOneTwoRoots p` — the root-count
    input the Markov uniqueness reduction needs at prime maxima.  (Symmetry by `le_total`;
    the ordered case is `two_roots_ordered`.) -/
theorem two_roots_of_prime (p : Nat) (hp : 1 < p)
    (hpg : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1)
    (x y : Nat) (hx : x < p) (hy : y < p)
    (hxr : (x * x + 1) % p = 0) (hyr : (y * y + 1) % p = 0) :
    x = y ∨ x + y = p := by
  have pos : ∀ z, (z * z + 1) % p = 0 → 1 ≤ z := by
    intro z hz
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · exfalso
      rw [h0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hp] at hz
      exact absurd hz (by decide)
    · exact h0
  have hx1 : 1 ≤ x := pos x hxr
  have hy1 : 1 ≤ y := pos y hyr
  rcases Nat.le_total y x with hyx | hxy
  · obtain ⟨d, hd⟩ := Nat.le.dest hyx
    rw [← hd] at hx hxr
    rcases two_roots_ordered p y d hp hpg hx hy1 hxr hyr with h | h
    · left; rw [← hd, h, Nat.add_zero]
    · right; rw [← hd]; exact h
  · obtain ⟨d, hd⟩ := Nat.le.dest hxy
    rw [← hd] at hy hyr
    rcases two_roots_ordered p x d hp hpg hy hx1 hyr hxr with h | h
    · left; rw [← hd, h, Nat.add_zero]
    · right; rw [← hd, Nat.add_comm x (x + d)]; exact h

/-- ★ Concrete: `x² ≡ −1 (mod 5)` has at most two roots (`5 ≡ 1 mod 4`, roots `{2,3}`,
    `2+3 = 5`), via the repo's `prime_gcd_5`.  So `SqrtNegOneTwoRoots 5` holds for the general
    (non-`decide`) reason — the prime case of the uniqueness reduction's root-count input. -/
theorem two_roots_5 (x y : Nat) (hx : x < 5) (hy : y < 5)
    (hxr : (x * x + 1) % 5 = 0) (hyr : (y * y + 1) % 5 = 0) :
    x = y ∨ x + y = 5 :=
  two_roots_of_prime 5 (by decide) E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_5 x y hx hy hxr hyr

end E213.Lib.Math.ModArith.MarkovPrimeFactor
