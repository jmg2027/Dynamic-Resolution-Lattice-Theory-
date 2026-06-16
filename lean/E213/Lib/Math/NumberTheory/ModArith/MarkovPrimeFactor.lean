import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT

/-!
# MarkovPrimeFactor — `x² ≡ −1 (mod p)` is unsolvable for `p ≡ 3 (mod 4)`

The Markov uniqueness arc (`Real213/Markov/MarkovUniqueness`) showed every Markov number `c` carries a
square root of `−1` mod `c`.  A prime `p ∣ c` then has `x² ≡ −1 (mod p)` solvable.  But this is
**unsolvable when `p ≡ 3 (mod 4)`** — so no prime `≡ 3 (mod 4)` divides a Markov number; every
odd prime factor is `≡ 1 (mod 4)` (Zhang 2007).

This file proves that obstruction *generally* (`MarkovUniqueness` had only finitary `decide`
instances), via the repo's ∅-axiom Fermat little theorem (`universal_flt_main`).  If `x² ≡ −1`
then `x^(p−1) = (x²)^((p−1)/2) ≡ (−1)^((p−1)/2)`; for `p = 4k+3` the exponent `(p−1)/2 = 2k+1`
is odd, so this is `≡ −1`, contradicting Fermat's `x^(p−1) ≡ 1` (forcing `p ∣ 2`).

Self-contained modular pieces first: `(p−1)² ≡ 1` and `(p−1)^(odd) ≡ p−1` mod `p`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

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
  have hid : (e + 1) * (e + 1) = (e + 2) * e + 1 := by ring_nat
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

open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)

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
  no_sqrt_neg_one_4k3 1 x E213.Lib.Math.NumberTheory.ModArith.UniversalFLT.prime_gcd_7 hx0 hxlt

/-- `x² ≡ −1 (mod 11)` is impossible (`11 = 4·2+3`), via `prime_gcd_11`. -/
theorem no_sqrt_neg_one_mod_11 (x : Nat) (hx0 : 0 < x) (hxlt : x < 11) :
    ¬ ((11 : Nat) ∣ (x * x + 1)) :=
  no_sqrt_neg_one_4k3 2 x E213.Lib.Math.NumberTheory.ModArith.UniversalFLT.prime_gcd_11 hx0 hxlt

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

/-- `a ∣ b → b ∣ c → a ∣ c`.  ∅-axiom (manual, avoids the leaky core `Nat.dvd_trans`). -/
theorem dvd_trans_loc (a b c : Nat) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨s, hs⟩ := hab; obtain ⟨t, ht⟩ := hbc
  exact ⟨s * t, by rw [ht, hs, E213.Tactic.NatHelper.mul_assoc]⟩

/-- `0 < b → a ∣ b → a ≤ b`.  ∅-axiom (core `le_of_dvd_loc` leaks `propext`). -/
theorem le_of_dvd_loc {a b : Nat} (hb : 0 < b) (h : a ∣ b) : a ≤ b := by
  obtain ⟨c, hc⟩ := h
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · rw [h0, Nat.mul_zero] at hc; rw [hc] at hb; exact absurd hb (Nat.lt_irrefl 0)
  · calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * c := Nat.mul_le_mul_left a h0
      _ = b := hc.symm

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

/-- `(y+d)² = y² + d·(2y+d)`.  ∅-axiom — `ring_nat` (main's reflection ring for `ℕ`). -/
theorem sq_expand (y d : Nat) : (y + d) * (y + d) = y * y + d * (2 * y + d) := by
  ring_nat

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
open E213.Lib.Math.NumberTheory.ModArith.ModBezoutInvariant (modBezout_inverse_correct)

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
  two_roots_of_prime 5 (by decide) E213.Lib.Math.NumberTheory.ModArith.UniversalFLT.prime_gcd_5 x y hx hy hxr hyr

/-- Prime-gcd hypothesis at `p = 13` (enumeration, per the `prime_gcd_5/7/11` pattern). -/
theorem prime_gcd_13 : ∀ m, 0 < m → m < 13 → (modBezout m 13).1 = 1 := by
  intro m hm hmlt
  match m with
  | 0 => exact absurd hm (Nat.lt_irrefl 0)
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | 10 => decide
  | 11 => decide
  | 12 => decide
  | n + 13 => exact absurd hmlt (Nat.not_lt_of_le (Nat.le_add_left 13 n))

/-- ★★ Concrete at a **prime Markov number**: `x² ≡ −1 (mod 13)` has at most two roots
    (`13 ≡ 1 mod 4`, roots `{5,8}`, `5+8 = 13`).  So `SqrtNegOneTwoRoots 13` holds for the
    *general* prime reason — and `13` is the maximum of the Markov triple `(1,5,13)`, so this is
    the root-count input the uniqueness reduction needs at an actual prime Markov number. -/
theorem two_roots_13 (x y : Nat) (hx : x < 13) (hy : y < 13)
    (hxr : (x * x + 1) % 13 = 0) (hyr : (y * y + 1) % 13 = 0) :
    x = y ∨ x + y = 13 :=
  two_roots_of_prime 13 (by decide) prime_gcd_13 x y hx hy hxr hyr

/-! ## §7 — `gcd = 1 ⟹ a modular inverse exists` (xgcd correctness)

The keystone bridging coprimality (which `markov_reachable_gcd_bc` supplies as `gcd213 b c = 1`)
to the encoding's invertibility hypothesis: **`gcd213 a m = 1 ⟹ ∃ x, (a·x) % m = 1 % m`**.  Its
core is that the gcd-component of `modBezout` (computed by `xgcdAux`) **divides both inputs** —
proved by an invariant under the bound `fuel ≥ r₁ + 1` (which `modBezout`'s `a+m+1` satisfies
since `a+m+1 ≥ m+1`).  Then `(modBezout a m).1 ∣ gcd213 a m = 1`, so it is `1`, and
`modBezout_inverse_correct` yields the inverse. -/

open E213.Lib.Math.NumberTheory.ModArith.ModBezout (xgcdAux bezoutSubMod)
open E213.Meta.Nat.Gcd213 (dvd_add_213 gcd213_greatest gcd213_dvd_left gcd213_dvd_right
  mul_eq_one_left)
open E213.Tactic.NatHelper (gcd213)

/-- ★★★★ **The `xgcdAux` gcd-component divides both inputs**, under `fuel ≥ r₁ + 1` (which
    rules out fuel-exhaustion: `r₁` strictly decreases, so the bound propagates and the
    recursion reaches `r₁ = 0`).  Induction on fuel. -/
theorem xgcdAux_dvd_both (p : Nat) :
    ∀ (fuel r₀ r₁ x₀ x₁ : Nat), r₁ + 1 ≤ fuel →
      (xgcdAux p fuel r₀ r₁ x₀ x₁).1 ∣ r₀ ∧ (xgcdAux p fuel r₀ r₁ x₀ x₁).1 ∣ r₁ := by
  intro fuel
  induction fuel with
  | zero => intro r₀ r₁ x₀ x₁ h; exact absurd h (Nat.not_succ_le_zero r₁)
  | succ f ih =>
    intro r₀ r₁ x₀ x₁ h
    match r₁ with
    | 0 => exact ⟨⟨1, (Nat.mul_one r₀).symm⟩, ⟨0, (Nat.mul_zero r₀).symm⟩⟩
    | k + 1 =>
      have hmod : r₀ % (k + 1) < k + 1 := Nat.mod_lt r₀ (Nat.zero_lt_succ k)
      have hbound : r₀ % (k + 1) + 1 ≤ f :=
        Nat.le_trans hmod (Nat.le_of_succ_le_succ h)
      have ihr := ih (k + 1) (r₀ % (k + 1)) x₁ (bezoutSubMod p (r₀ / (k + 1)) x₀ x₁) hbound
      refine ⟨?_, ihr.1⟩
      have hdm : (k + 1) * (r₀ / (k + 1)) + r₀ % (k + 1) = r₀ :=
        E213.Meta.Nat.AddMod213.div_add_mod r₀ (k + 1)
      have hsum := dvd_add_213 _ _ _
        (dvd_mul_right_loc _ (k + 1) (r₀ / (k + 1)) ihr.1) ihr.2
      rwa [hdm] at hsum

/-- `(modBezout a m).1` divides both `a` and `m`. -/
theorem modBezout_dvd_both (a m : Nat) : (modBezout a m).1 ∣ a ∧ (modBezout a m).1 ∣ m :=
  xgcdAux_dvd_both m (a + m + 1) a m 1 0 (Nat.le_add_left (m + 1) a)

/-- `gcd213 a m = 1 ⟹ (modBezout a m).1 = 1`: the xgcd gcd-component divides `gcd213 a m`. -/
theorem modBezout_gcd_one (a m : Nat) (h : gcd213 a m = 1) : (modBezout a m).1 = 1 := by
  obtain ⟨hda, hdm⟩ := modBezout_dvd_both a m
  have hdvd1 : (modBezout a m).1 ∣ 1 := h ▸ gcd213_greatest a m (modBezout a m).1 hda hdm
  obtain ⟨k, hk⟩ := hdvd1
  exact mul_eq_one_left (modBezout a m).1 k hk.symm

/-- ★★★★★ **Inverse from coprimality.**  `gcd213 a m = 1` and `0 < m` give an explicit modular
    inverse: `(a · (modBezout a m).2) % m = 1 % m`.  Closes the C2→C4 bridge — combined with
    `markov_reachable_gcd_bc` the `√(−1)` encoding fires unconditionally on every tree triple. -/
theorem inverse_of_coprime (a m : Nat) (hm : 0 < m) (h : gcd213 a m = 1) :
    (a * (modBezout a m).2) % m = 1 % m :=
  modBezout_inverse_correct a m hm (modBezout_gcd_one a m h)

/-- ★★★★★ **Euclid's lemma, fully general.**  `gcd213 a m = 1 ∧ m ∣ a·b ⟹ m ∣ b` for any
    modulus `m > 1` — coprime cancellation, no inverse hypothesis (the inverse is produced from
    coprimality by `inverse_of_coprime`).  A reusable ∅-axiom number-theory primitive. -/
theorem euclid_of_coprime (a b m : Nat) (hm : 1 < m) (hco : gcd213 a m = 1) (hdvd : m ∣ (a * b)) :
    m ∣ b := by
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hm)
  have hinv : (a * (modBezout a m).2) % m = 1 := by
    rw [inverse_of_coprime a m hmpos hco, Nat.mod_eq_of_lt hm]
  exact euclid_via_inverse m a b (modBezout a m).2 hinv hdvd

/-! ## §8 — prime-power coprimality (toward the Button/Zhang case)

With Euclid's lemma in hand, the structure of divisors of `pᵏ`: a "prime" `p` (divisors only
`1, p`) makes every divisor of `pᵏ` either `1` or divisible by `p`, hence `gcd(n, pᵏ) = 1`
whenever `p ∤ n`.  This is the coprimality the prime-power two-roots theorem needs. -/

/-- For a prime `p` (`hpr`: divisors are `1` or `p`), `p ∤ n ⟹ gcd213 p n = 1`. -/
theorem prime_coprime (p n : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hn : ¬ p ∣ n) :
    gcd213 p n = 1 := by
  rcases hpr (gcd213 p n) (gcd213_dvd_left p n) with h1 | hp
  · exact h1
  · exact absurd (hp ▸ gcd213_dvd_right p n) hn

/-- **Divisors of a prime power are `1` or divisible by `p`.**  `d ∣ pᵏ ⟹ d = 1 ∨ p ∣ d`.
    Induction on `k`, cancelling one `p` via `euclid_of_coprime` when `p ∤ d`. -/
theorem dvd_prime_pow_cases (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ (k d : Nat), d ∣ p ^ k → d = 1 ∨ p ∣ d := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  intro k
  induction k with
  | zero =>
    intro d hd
    obtain ⟨c, hc⟩ := hd
    exact Or.inl (mul_eq_one_left d c hc.symm)
  | succ k ih =>
    intro d hd
    have hpowpos : 0 < p ^ (k + 1) := Nat.pos_pow_of_pos (k + 1) hppos
    have hdne : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0] at hd
        obtain ⟨c, hc⟩ := hd
        rw [Nat.zero_mul] at hc
        exact absurd hc (Nat.ne_of_gt hpowpos)
      · exact h0
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hd2) hdne)
    · -- split on gcd213 p d = 1 ∨ = p (pure; avoids Decidable (∣))
      rcases hpr (gcd213 p d) (gcd213_dvd_left p d) with hco | hgp
      · have hdvd' : d ∣ p * p ^ k := by
          have h1 : d ∣ p ^ k * p := (Nat.pow_succ p k) ▸ hd
          rwa [Nat.mul_comm] at h1
        exact ih d (euclid_of_coprime p (p ^ k) d hd2 hco hdvd')
      · exact Or.inr (hgp ▸ gcd213_dvd_right p d)

/-- `p ∤ n ⟹ gcd213 n (pᵏ) = 1` for a prime `p`. -/
theorem coprime_prime_pow (p n : Nat) (hp2 : 2 ≤ p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hn : ¬ p ∣ n) (k : Nat) : gcd213 n (p ^ k) = 1 := by
  rcases dvd_prime_pow_cases p hp2 hpr k (gcd213 n (p ^ k)) (gcd213_dvd_right n (p ^ k))
    with h | hp
  · exact h
  · -- p ∣ gcd213 n (p^k) ∣ n  ⟹  p ∣ n, contradicting hn (manual transitivity)
    obtain ⟨c, hc⟩ := hp
    obtain ⟨e, he⟩ := gcd213_dvd_left n (p ^ k)
    exact absurd ⟨c * e, by rw [he, hc]; exact E213.Tactic.NatHelper.mul_assoc p c e⟩ hn

/-! ## §9 — ≤ 2 roots mod a prime power (the Button/Zhang case) -/

/-- Ordered core for a prime-power modulus `m` (`p` prime, `p ∣ m`, coprimality supplied by
    `hcop`).  With `x = y+d`, `m ∣ d·(2y+d)`; `p` divides at most one of `d, 2y+d` (else `p ∣ x`,
    impossible), so the other is coprime to `m` and cancels, giving `d = 0` or `(y+d)+y = m`. -/
theorem two_roots_pow_ordered (p m y d : Nat) (hp3 : 3 ≤ p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hpm : p ∣ m) (hm1 : 1 < m)
    (hcop : ∀ n, ¬ p ∣ n → gcd213 n m = 1)
    (hlt : y + d < m) (hy1 : 1 ≤ y)
    (hxr : ((y + d) * (y + d) + 1) % m = 0) (hyr : (y * y + 1) % m = 0) :
    d = 0 ∨ (y + d) + y = m := by
  have hp2 : 2 ≤ p := Nat.le_trans (by decide) hp3
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp3
  -- p ∤ 2  (else p ≤ 2 < 3)
  have hp_not2 : ¬ p ∣ 2 := fun h =>
    absurd (Nat.le_trans hp3 (le_of_dvd_loc (by decide) h)) (by decide)
  -- m ∣ d·(2y+d)
  have hX : m ∣ ((y + d) * (y + d) + 1) := dvd_of_mod_eq_zero hxr
  have hY : m ∣ (y * y + 1) := dvd_of_mod_eq_zero hyr
  have hdiff : m ∣ (d * (2 * y + d)) := by
    have hle : y * y + 1 ≤ (y + d) * (y + d) + 1 := by
      rw [sq_expand]; exact Nat.add_le_add_right (Nat.le_add_right _ _) 1
    have hs := dvd_sub_213 (y * y + 1) ((y + d) * (y + d) + 1) m hle hY hX
    have heq : (y + d) * (y + d) + 1 - (y * y + 1) = d * (2 * y + d) := by
      rw [sq_expand, Nat.add_right_comm (y * y) (d * (2 * y + d)) 1,
          Nat.add_comm (y * y + 1) (d * (2 * y + d)), E213.Tactic.NatHelper.add_sub_cancel_right]
    rwa [heq] at hs
  -- p ∤ (y+d)  (= x)
  have hpx : ¬ p ∣ (y + d) := by
    intro hpd
    have hpX : p ∣ ((y + d) * (y + d) + 1) := dvd_trans_loc p m _ hpm hX
    have hpsq : p ∣ (y + d) * (y + d) := dvd_mul_right_loc p (y + d) (y + d) hpd
    have hp1' : p ∣ 1 := by
      have := dvd_sub_213 ((y + d) * (y + d)) ((y + d) * (y + d) + 1) p
        (Nat.le_succ _) hpsq hpX
      rwa [E213.Tactic.NatHelper.succ_sub] at this
    exact absurd (Nat.le_trans hp3 (le_of_dvd_loc (by decide) hp1')) (by decide)
  -- 2y+d = (y+d)+y
  have hsum : 2 * y + d = (y + d) + y := by rw [two_mul, Nat.add_right_comm y y d]
  have hpos : 0 < (y + d) + y :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hy1 (Nat.le_add_left y (y + d)))
  have hlt2 : (y + d) + y < 2 * m := by
    rw [two_mul]; exact Nat.add_lt_add hlt (Nat.lt_of_le_of_lt (Nat.le_add_right y d) hlt)
  -- split on gcd213 p d = 1 (p∤d) or = p (p∣d)
  rcases hpr (gcd213 p d) (gcd213_dvd_left p d) with hg1 | hgp
  · -- p ∤ d ⟹ gcd(d,m)=1 ⟹ m ∣ (2y+d) = (y+d)+y ⟹ = m
    right
    have hpd : ¬ p ∣ d := by
      intro hpd
      have : p ∣ gcd213 p d := gcd213_greatest p d p ⟨1, (Nat.mul_one p).symm⟩ hpd
      rw [hg1] at this
      exact absurd (le_of_dvd_loc (by decide) this) (by
        exact Nat.not_le_of_lt hp1)
    have h2yd : m ∣ (2 * y + d) :=
      euclid_of_coprime d (2 * y + d) m hm1 (hcop d hpd) hdiff
    rw [hsum] at h2yd
    exact eq_p_of_dvd m ((y + d) + y) hm1 hpos hlt2 h2yd
  · -- p ∣ d ⟹ p ∤ (2y+d) ⟹ gcd(2y+d,m)=1 ⟹ m ∣ d ⟹ d = 0
    left
    have hpd : p ∣ d := hgp ▸ gcd213_dvd_right p d
    have hp_not : ¬ p ∣ (2 * y + d) := by
      intro hp2yd
      -- p∣d, p∣(2y+d) ⟹ p∣2y ⟹ p∣y ⟹ p∣(y+d), contra hpx
      have hp2y : p ∣ (2 * y) := by
        have := dvd_sub_213 d (2 * y + d) p (Nat.le_add_left d (2 * y)) hpd hp2yd
        rwa [E213.Tactic.NatHelper.add_sub_cancel_right] at this
      have hpy : p ∣ y := euclid_of_coprime 2 y p hp1
        (by rw [E213.Meta.Nat.Gcd213.gcd213_comm]; exact prime_coprime p 2 hpr hp_not2) hp2y
      exact hpx (dvd_add_213 p y d hpy hpd)
    have hmd : m ∣ d := euclid_of_coprime (2 * y + d) d m hm1 (hcop (2 * y + d) hp_not)
      (by rw [Nat.mul_comm] at hdiff; exact hdiff)
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact h0
    · exact absurd (le_of_dvd_loc h0 hmd)
        (Nat.not_le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left d y) hlt))

/-- ★★★★★ **≤ 2 roots of `x² ≡ −1` mod a prime power** (`p` odd prime, `m = p^(k+1)`).  Any two
    roots `x, y < m` satisfy `x = y ∨ x + y = m` — i.e. `SqrtNegOneTwoRoots (p^(k+1))`, the
    Button/Zhang prime-power input the uniqueness reduction needs.  `p` divides at most one of
    `x−y, x+y` (else `p ∣ x`, impossible since `x² ≡ −1`), and the coprime one cancels. -/
theorem two_roots_of_prime_pow (p k : Nat) (hp3 : 3 ≤ p) (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p)
    (x y : Nat) (hx : x < p ^ (k + 1)) (hy : y < p ^ (k + 1))
    (hxr : (x * x + 1) % p ^ (k + 1) = 0) (hyr : (y * y + 1) % p ^ (k + 1) = 0) :
    x = y ∨ x + y = p ^ (k + 1) := by
  have hp2 : 2 ≤ p := Nat.le_trans (by decide) hp3
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hpm : p ∣ p ^ (k + 1) := ⟨p ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have hm1 : 1 < p ^ (k + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide) hp3)
      (le_of_dvd_loc (Nat.pos_pow_of_pos _ hppos) hpm)
  have hcop : ∀ n, ¬ p ∣ n → gcd213 n (p ^ (k + 1)) = 1 :=
    fun n hn => coprime_prime_pow p n hp2 hpr hn (k + 1)
  have pos : ∀ z, (z * z + 1) % p ^ (k + 1) = 0 → 1 ≤ z := by
    intro z hz
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · rw [h0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hm1] at hz
      exact absurd hz (by decide)
    · exact h0
  have hx1 : 1 ≤ x := pos x hxr
  have hy1 : 1 ≤ y := pos y hyr
  rcases Nat.le_total y x with hyx | hxy
  · obtain ⟨d, hd⟩ := Nat.le.dest hyx
    rw [← hd] at hx hxr
    rcases two_roots_pow_ordered p (p ^ (k + 1)) y d hp3 hpr hpm hm1 hcop hx hy1 hxr hyr with h | h
    · left; rw [← hd, h, Nat.add_zero]
    · right; rw [← hd]; exact h
  · obtain ⟨d, hd⟩ := Nat.le.dest hxy
    rw [← hd] at hy hyr
    rcases two_roots_pow_ordered p (p ^ (k + 1)) x d hp3 hpr hpm hm1 hcop hy hx1 hyr hxr with h | h
    · left; rw [← hd, h, Nat.add_zero]
    · right; rw [← hd, Nat.add_comm x (x + d)]; exact h

/-! ### The `2·pᵏ` two-roots family (CRT recombination of the prime-power split)

The prime-power split (`two_roots_pow_ordered`) needs `∀ n, ¬p∣n → gcd(n, m) = 1` — which fails for
`m = 2·pᵏ` (the factor `2` is `p`-coprime but not `m`-coprime).  Markov numbers include even values
(`34 = 2·17`, `194 = 2·97`), exactly the `2·pᵏ` shape (`p ≡ 1 mod 4`).  Here the two-roots fact is
recovered for `m = 2·pᵏ` by **CRT recombination**: reduce a root mod `2·pᵏ` to a root mod `pᵏ` (reuse
`two_roots_of_prime_pow`), force oddness mod `2`, and recombine via `2·pᵏ ∣ a` from `2 ∣ a ∧ pᵏ ∣ a`
(coprimality of `2` and the odd `pᵏ`). -/

/-- `P ∣ x² − (x % P)²` — the square reduces mod `P` (pure: `div_add_mod` + `ring_nat`). -/
theorem dvd_sq_sub_mod_sq (P x : Nat) : P ∣ (x * x - (x % P) * (x % P)) := by
  have hdm : P * (x / P) + x % P = x := E213.Meta.Nat.AddMod213.div_add_mod x P
  refine ⟨P * (x / P) * (x / P) + 2 * (x / P) * (x % P), ?_⟩
  have hsq : x * x = (P * (x / P) + x % P) * (P * (x / P) + x % P) := by rw [hdm]
  have hexp : (P * (x / P) + x % P) * (P * (x / P) + x % P)
            = (x % P) * (x % P) + P * (P * (x / P) * (x / P) + 2 * (x / P) * (x % P)) := by ring_nat
  rw [hsq, hexp, Nat.add_comm, E213.Tactic.NatHelper.add_sub_cancel_right]

/-- A root mod `2·…` reduces to a root mod `P`: `P ∣ x²+1 ⟹ (x%P)²+1 ≡ 0 (mod P)`. -/
theorem root_mod_P (P x : Nat) (hP1 : 1 < P) (hPx : P ∣ (x * x + 1)) :
    ((x % P) * (x % P) + 1) % P = 0 := by
  have hd : P ∣ (x * x - (x % P) * (x % P)) := dvd_sq_sub_mod_sq P x
  have hle : (x % P) * (x % P) ≤ x * x := Nat.mul_le_mul (Nat.mod_le x P) (Nat.mod_le x P)
  have hle2 : (x * x - (x % P) * (x % P)) ≤ (x * x + 1) :=
    Nat.le_trans (Nat.sub_le _ _) (Nat.le_succ _)
  have hsub : P ∣ ((x * x + 1) - (x * x - (x % P) * (x % P))) := dvd_sub_213 _ _ P hle2 hd hPx
  have heq : (x * x + 1) - (x * x - (x % P) * (x % P)) = (x % P) * (x % P) + 1 := by
    have hAcancel : (x * x - (x % P) * (x % P)) + (x % P) * (x % P) = x * x :=
      E213.Tactic.NatHelper.sub_add_cancel hle
    have hA1 : x * x + 1 = (x * x - (x % P) * (x % P)) + ((x % P) * (x % P) + 1) := by
      rw [← Nat.add_assoc, hAcancel]
    rw [hA1, Nat.add_comm (x * x - (x % P) * (x % P)) _,
        E213.Tactic.NatHelper.add_sub_cancel_right]
  rw [heq] at hsub
  obtain ⟨w, hw⟩ := hsub
  rw [hw]; exact E213.Tactic.NatHelper.mul_mod_right P w

/-- `M ∣ d` and `d < M` give `d = 0`. -/
private theorem eq_zero_of_dvd_lt {M d : Nat} (hd : M ∣ d) (hlt : d < M) : d = 0 := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exact h
  · exact absurd (le_of_dvd_loc h hd) (Nat.not_le_of_lt hlt)

/-- `2 ∣ x²+1 ⟹ x` is odd (`x % 2 = 1`). -/
private theorem odd_of_two_dvd_sq_succ (x : Nat) (h : 2 ∣ (x * x + 1)) : x % 2 = 1 := by
  rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one x with h0 | h1
  · exfalso
    have h2x : 2 ∣ x := dvd_of_mod_eq_zero h0
    have h2xx : 2 ∣ (x * x) := dvd_mul_right_loc 2 x x h2x
    have h21 : 2 ∣ 1 := by
      have hs := dvd_sub_213 (x * x) (x * x + 1) 2 (Nat.le_succ _) h2xx h
      rwa [E213.Tactic.NatHelper.succ_sub] at hs
    exact absurd (le_of_dvd_loc (by decide) h21) (by decide)
  · exact h1

/-- `M ∣ (x − y)` whenever `x ≡ y (mod M)` (pure: `add_sub_add_right` cancels the common residue). -/
private theorem dvd_sub_of_mod_eq (M x y : Nat) (hmod : x % M = y % M) : M ∣ (x - y) := by
  refine ⟨x / M - y / M, ?_⟩
  have hx : M * (x / M) + x % M = x := E213.Meta.Nat.AddMod213.div_add_mod x M
  have hy : M * (y / M) + y % M = y := E213.Meta.Nat.AddMod213.div_add_mod y M
  calc x - y
      = (M * (x / M) + x % M) - (M * (y / M) + y % M) := by rw [hx, hy]
    _ = (M * (x / M) + y % M) - (M * (y / M) + y % M) := by rw [hmod]
    _ = M * (x / M) - M * (y / M) := E213.Tactic.NatHelper.add_sub_add_right _ _ _
    _ = M * (x / M - y / M) := (E213.Tactic.NatHelper.mul_sub _ _ _).symm

/-- CRT: `2 ∣ a` and `P ∣ a` with `gcd(2,P)=1` give `2·P ∣ a`. -/
private theorem two_P_dvd (P a : Nat) (hP1 : 1 < P) (hco : gcd213 2 P = 1)
    (h2 : 2 ∣ a) (hP : P ∣ a) : 2 * P ∣ a := by
  obtain ⟨t, ht⟩ := h2
  have hPt : P ∣ t := euclid_of_coprime 2 t P hP1 hco (ht ▸ hP)
  obtain ⟨s, hs⟩ := hPt
  exact ⟨s, by rw [ht, hs]; exact (E213.Tactic.NatHelper.mul_assoc 2 P s).symm⟩

/-- ★★★★★ **≤ 2 roots of `x² ≡ −1` mod `2·p^(k+1)`** (`p` odd prime).  Any two roots `x, y < 2·p^(k+1)`
    satisfy `x = y ∨ x + y = 2·p^(k+1)` — i.e. `SqrtNegOneTwoRoots (2·p^(k+1))`, the input for Markov
    uniqueness on the **even** `2·pᵏ` family (`34 = 2·17`, `194 = 2·97`, …).  By CRT recombination of the
    prime-power split (`two_roots_of_prime_pow` mod `p^(k+1)`) with the odd-forcing mod `2`. -/
theorem two_roots_of_two_prime_pow (p k : Nat) (hp3 : 3 ≤ p) (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p)
    (x y : Nat) (hx : x < 2 * p ^ (k + 1)) (hy : y < 2 * p ^ (k + 1))
    (hxr : (x * x + 1) % (2 * p ^ (k + 1)) = 0) (hyr : (y * y + 1) % (2 * p ^ (k + 1)) = 0) :
    x = y ∨ x + y = 2 * p ^ (k + 1) := by
  have hp2 : 2 ≤ p := Nat.le_trans (by decide) hp3
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hPpos : 0 < p ^ (k + 1) := Nat.pos_pow_of_pos _ hppos
  have hpm : p ∣ p ^ (k + 1) := ⟨p ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have hP1 : 1 < p ^ (k + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide) hp3) (le_of_dvd_loc hPpos hpm)
  have hm1 : 1 < 2 * p ^ (k + 1) :=
    Nat.lt_of_lt_of_le hP1 (Nat.le_mul_of_pos_left _ (by decide))
  have hp_not2 : ¬ p ∣ 2 :=
    fun h => absurd (Nat.le_trans hp3 (le_of_dvd_loc (by decide) h)) (by decide)
  have hco : gcd213 2 (p ^ (k + 1)) = 1 := coprime_prime_pow p 2 hp2 hpr hp_not2 (k + 1)
  have hPdvdm : p ^ (k + 1) ∣ 2 * p ^ (k + 1) := ⟨2, by rw [Nat.mul_comm]⟩
  have h2dvdm : 2 ∣ 2 * p ^ (k + 1) := ⟨p ^ (k + 1), rfl⟩
  have hPx : p ^ (k + 1) ∣ (x * x + 1) := dvd_trans_loc _ _ _ hPdvdm (dvd_of_mod_eq_zero hxr)
  have hPy : p ^ (k + 1) ∣ (y * y + 1) := dvd_trans_loc _ _ _ hPdvdm (dvd_of_mod_eq_zero hyr)
  have h2x : 2 ∣ (x * x + 1) := dvd_trans_loc _ _ _ h2dvdm (dvd_of_mod_eq_zero hxr)
  have h2y : 2 ∣ (y * y + 1) := dvd_trans_loc _ _ _ h2dvdm (dvd_of_mod_eq_zero hyr)
  have hxodd : x % 2 = 1 := odd_of_two_dvd_sq_succ x h2x
  have hyodd : y % 2 = 1 := odd_of_two_dvd_sq_succ y h2y
  have hxr' : ((x % p ^ (k + 1)) * (x % p ^ (k + 1)) + 1) % p ^ (k + 1) = 0 :=
    root_mod_P (p ^ (k + 1)) x hP1 hPx
  have hyr' : ((y % p ^ (k + 1)) * (y % p ^ (k + 1)) + 1) % p ^ (k + 1) = 0 :=
    root_mod_P (p ^ (k + 1)) y hP1 hPy
  have hxlt' : x % p ^ (k + 1) < p ^ (k + 1) := Nat.mod_lt x hPpos
  have hylt' : y % p ^ (k + 1) < p ^ (k + 1) := Nat.mod_lt y hPpos
  rcases two_roots_of_prime_pow p k hp3 hpr (x % p ^ (k + 1)) (y % p ^ (k + 1))
      hxlt' hylt' hxr' hyr' with hEq | hSum
  · -- equal residues mod P ⟹ x = y (recombine with equal parity mod 2)
    left
    have hmod2 : x % 2 = y % 2 := by rw [hxodd, hyodd]
    have hPsub : p ^ (k + 1) ∣ (x - y) := dvd_sub_of_mod_eq (p ^ (k + 1)) x y hEq
    have h2sub : 2 ∣ (x - y) := dvd_sub_of_mod_eq 2 x y hmod2
    have hmsub : 2 * p ^ (k + 1) ∣ (x - y) := two_P_dvd (p ^ (k + 1)) (x - y) hP1 hco h2sub hPsub
    have hPsub' : p ^ (k + 1) ∣ (y - x) := dvd_sub_of_mod_eq (p ^ (k + 1)) y x hEq.symm
    have h2sub' : 2 ∣ (y - x) := dvd_sub_of_mod_eq 2 y x hmod2.symm
    have hmsub' : 2 * p ^ (k + 1) ∣ (y - x) := two_P_dvd (p ^ (k + 1)) (y - x) hP1 hco h2sub' hPsub'
    have hx0 : x - y = 0 :=
      eq_zero_of_dvd_lt hmsub (Nat.lt_of_le_of_lt (Nat.sub_le x y) hx)
    have hy0 : y - x = 0 :=
      eq_zero_of_dvd_lt hmsub' (Nat.lt_of_le_of_lt (Nat.sub_le y x) hy)
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hx0) (Nat.le_of_sub_eq_zero hy0)
  · -- residues sum to P ⟹ x + y = 2P (recombine with both odd)
    right
    have hPsum : p ^ (k + 1) ∣ (x + y) := by
      refine ⟨x / p ^ (k + 1) + y / p ^ (k + 1) + 1, ?_⟩
      have ex : p ^ (k + 1) * (x / p ^ (k + 1)) + x % p ^ (k + 1) = x := E213.Meta.Nat.AddMod213.div_add_mod x _
      have ey : p ^ (k + 1) * (y / p ^ (k + 1)) + y % p ^ (k + 1) = y := E213.Meta.Nat.AddMod213.div_add_mod y _
      calc x + y
          = (p ^ (k + 1) * (x / p ^ (k + 1)) + x % p ^ (k + 1))
            + (p ^ (k + 1) * (y / p ^ (k + 1)) + y % p ^ (k + 1)) := by rw [ex, ey]
        _ = p ^ (k + 1) * (x / p ^ (k + 1)) + p ^ (k + 1) * (y / p ^ (k + 1))
            + (x % p ^ (k + 1) + y % p ^ (k + 1)) := by ring_nat
        _ = p ^ (k + 1) * (x / p ^ (k + 1)) + p ^ (k + 1) * (y / p ^ (k + 1)) + p ^ (k + 1) := by
              rw [hSum]
        _ = p ^ (k + 1) * (x / p ^ (k + 1) + y / p ^ (k + 1) + 1) := by ring_nat
    have h2sum : 2 ∣ (x + y) := by
      refine ⟨x / 2 + y / 2 + 1, ?_⟩
      have ex : 2 * (x / 2) + x % 2 = x := E213.Meta.Nat.AddMod213.div_add_mod x _
      have ey : 2 * (y / 2) + y % 2 = y := E213.Meta.Nat.AddMod213.div_add_mod y _
      calc x + y
          = (2 * (x / 2) + x % 2) + (2 * (y / 2) + y % 2) := by rw [ex, ey]
        _ = 2 * (x / 2) + 2 * (y / 2) + (x % 2 + y % 2) := by ring_nat
        _ = 2 * (x / 2) + 2 * (y / 2) + (1 + 1) := by rw [hxodd, hyodd]
        _ = 2 * (x / 2 + y / 2 + 1) := by ring_nat
    have hmsum : 2 * p ^ (k + 1) ∣ (x + y) := two_P_dvd (p ^ (k + 1)) (x + y) hP1 hco h2sum hPsum
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exfalso; rw [h, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hm1] at hxr
        exact absurd hxr (by decide)
      · exact h
    exact eq_p_of_dvd (2 * p ^ (k + 1)) (x + y) hm1
      (Nat.lt_of_lt_of_le hx1 (Nat.le_add_right x y))
      (by rw [Nat.two_mul]; exact Nat.add_lt_add hx hy) hmsum

/-! ### Prime-power square collapse (residue-free) — the Zhang `3c±2` bridge core

The core of `two_roots_pow_ordered` is residue-free: `m = p^(k+1) ∣ d·(2y+d) = (y+d)²−y²` with
`p ∤ (y+d)` collapses to `d = 0 ∨ (y+d)+y = m`.  The `+1` of the `√(−1)` case only supplied `p ∤ (y+d)`.
Taken as a hypothesis, the collapse serves any residue — in particular `x² ≡ y² (mod m)` with `p ∤ x,y`
(`sq_eq_collapse_pp`), the form Zhang's `3c±2` route needs (`δ² ≡ −c² (mod M)`). -/

/-- Prime-power square collapse (residue-free): `m = p^(k+1)`, `m ∣ d·(2y+d)`, `p ∤ (y+d)`, `1 ≤ y`,
    `y+d < m` ⟹ `d = 0 ∨ (y+d)+y = m`. -/
theorem sq_collapse_pow_ordered (p m y d : Nat) (hp3 : 3 ≤ p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hpm : p ∣ m) (hm1 : 1 < m)
    (hcop : ∀ n, ¬ p ∣ n → gcd213 n m = 1)
    (hlt : y + d < m) (hy1 : 1 ≤ y) (hpx : ¬ p ∣ (y + d))
    (hdiff : m ∣ (d * (2 * y + d))) : d = 0 ∨ (y + d) + y = m := by
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp3
  have hp_not2 : ¬ p ∣ 2 :=
    fun h => absurd (Nat.le_trans hp3 (le_of_dvd_loc (by decide) h)) (by decide)
  have hsum : 2 * y + d = (y + d) + y := by rw [two_mul, Nat.add_right_comm y y d]
  have hpos : 0 < (y + d) + y :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hy1 (Nat.le_add_left y (y + d)))
  have hlt2 : (y + d) + y < 2 * m := by
    rw [two_mul]; exact Nat.add_lt_add hlt (Nat.lt_of_le_of_lt (Nat.le_add_right y d) hlt)
  rcases hpr (gcd213 p d) (gcd213_dvd_left p d) with hg1 | hgp
  · right
    have hpd : ¬ p ∣ d := by
      intro hpd
      have : p ∣ gcd213 p d := gcd213_greatest p d p ⟨1, (Nat.mul_one p).symm⟩ hpd
      rw [hg1] at this
      exact absurd (le_of_dvd_loc (by decide) this) (Nat.not_le_of_lt hp1)
    have h2yd : m ∣ (2 * y + d) := euclid_of_coprime d (2 * y + d) m hm1 (hcop d hpd) hdiff
    rw [hsum] at h2yd
    exact eq_p_of_dvd m ((y + d) + y) hm1 hpos hlt2 h2yd
  · left
    have hpd : p ∣ d := hgp ▸ gcd213_dvd_right p d
    have hp_not : ¬ p ∣ (2 * y + d) := by
      intro hp2yd
      have hp2y : p ∣ (2 * y) := by
        have := dvd_sub_213 d (2 * y + d) p (Nat.le_add_left d (2 * y)) hpd hp2yd
        rwa [E213.Tactic.NatHelper.add_sub_cancel_right] at this
      have hpy : p ∣ y := euclid_of_coprime 2 y p hp1
        (by rw [E213.Meta.Nat.Gcd213.gcd213_comm]; exact prime_coprime p 2 hpr hp_not2) hp2y
      exact hpx (dvd_add_213 p y d hpy hpd)
    have hmd : m ∣ d := euclid_of_coprime (2 * y + d) d m hm1 (hcop (2 * y + d) hp_not)
      (by rw [Nat.mul_comm] at hdiff; exact hdiff)
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact h0
    · exact absurd (le_of_dvd_loc h0 hmd)
        (Nat.not_le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left d y) hlt))

/-- ★★★★★ **Prime-power square equality**: for `m = p^(k+1)` (odd prime `p`), if `x² ≡ y² (mod m)` with
    `p ∤ x` and `p ∤ y`, then `x = y ∨ x + y = m`.  The residue-free generalization of
    `two_roots_of_prime_pow` — Zhang's `3c±2` route applies it to `δ² ≡ −c² (mod M)`. -/
theorem sq_eq_collapse_pp (p k x y : Nat) (hp3 : 3 ≤ p) (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p)
    (hx : x < p ^ (k + 1)) (hy : y < p ^ (k + 1)) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y)
    (hsq : (x * x) % p ^ (k + 1) = (y * y) % p ^ (k + 1)) : x = y ∨ x + y = p ^ (k + 1) := by
  have hp2 : 2 ≤ p := Nat.le_trans (by decide) hp3
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hpm : p ∣ p ^ (k + 1) := ⟨p ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have hm1 : 1 < p ^ (k + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide) hp3) (le_of_dvd_loc (Nat.pos_pow_of_pos _ hppos) hpm)
  have hcop : ∀ n, ¬ p ∣ n → gcd213 n (p ^ (k + 1)) = 1 :=
    fun n hn => coprime_prime_pow p n hp2 hpr hn (k + 1)
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · exact absurd (by rw [h0]; exact ⟨0, (Nat.mul_zero p).symm⟩) hpy
    · exact h0
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · exact absurd (by rw [h0]; exact ⟨0, (Nat.mul_zero p).symm⟩) hpx
    · exact h0
  rcases Nat.le_total y x with hyx | hxy
  · obtain ⟨d, hd⟩ := Nat.le.dest hyx
    have hdiff : p ^ (k + 1) ∣ (d * (2 * y + d)) := by
      have hd1 : p ^ (k + 1) ∣ (x * x - y * y) := dvd_sub_of_mod_eq (p ^ (k + 1)) (x * x) (y * y) hsq
      rw [← hd, sq_expand y d, Nat.add_comm (y * y) (d * (2 * y + d)),
          E213.Tactic.NatHelper.add_sub_cancel_right] at hd1
      exact hd1
    have hpx' : ¬ p ∣ (y + d) := by rw [hd]; exact hpx
    have hlt : y + d < p ^ (k + 1) := by rw [hd]; exact hx
    rcases sq_collapse_pow_ordered p (p ^ (k + 1)) y d hp3 hpr hpm hm1 hcop hlt hy1 hpx' hdiff with h | h
    · left; rw [← hd, h, Nat.add_zero]
    · right; rw [← hd]; exact h
  · obtain ⟨d, hd⟩ := Nat.le.dest hxy
    have hdiff : p ^ (k + 1) ∣ (d * (2 * x + d)) := by
      have hd1 : p ^ (k + 1) ∣ (y * y - x * x) :=
        dvd_sub_of_mod_eq (p ^ (k + 1)) (y * y) (x * x) hsq.symm
      rw [← hd, sq_expand x d, Nat.add_comm (x * x) (d * (2 * x + d)),
          E213.Tactic.NatHelper.add_sub_cancel_right] at hd1
      exact hd1
    have hpx' : ¬ p ∣ (x + d) := by rw [hd]; exact hpy
    have hlt : x + d < p ^ (k + 1) := by rw [hd]; exact hy
    rcases sq_collapse_pow_ordered p (p ^ (k + 1)) x d hp3 hpr hpm hm1 hcop hlt hx1 hpx' hdiff with h | h
    · left; rw [← hd, h, Nat.add_zero]
    · right; rw [← hd, Nat.add_comm x (x + d)]; exact h

/-- **`√M`-bounded primality**: if no `d` with `2 ≤ d`, `d² ≤ M` divides `M`, then `M` is prime
    (`∀ e, e∣M → e = 1 ∨ e = M`).  A composite `M = e·f` with `2 ≤ e ≤ f` has `min` factor `e ≤ √M`
    (`e² ≤ e·f = M`), which the hypothesis forbids.  Lets primality of a concrete `M = 3c±2` be checked
    by a `√M`-bounded `decide` (the naive `∀d≤M` overflows the kernel). -/
theorem prime_of_no_small_factor (M : Nat) (hM : 2 ≤ M)
    (h : ∀ d, 2 ≤ d → d * d ≤ M → ¬ d ∣ M) : ∀ e, e ∣ M → e = 1 ∨ e = M := by
  intro e he
  obtain ⟨f, hf⟩ := he
  match e, f, hf with
  | 0, f, hf => rw [Nat.zero_mul] at hf; rw [hf] at hM; exact absurd hM (by decide)
  | 1, f, hf => exact Or.inl rfl
  | (n + 2), 0, hf => rw [Nat.mul_zero] at hf; rw [hf] at hM; exact absurd hM (by decide)
  | (n + 2), 1, hf => exact Or.inr (by rw [Nat.mul_one] at hf; exact hf.symm)
  | (n + 2), (m + 2), hf =>
      exfalso
      rcases Nat.le_total (n + 2) (m + 2) with hle | hle
      · exact h (n + 2) (Nat.le_add_left 2 n)
          (by rw [hf]; exact Nat.mul_le_mul (Nat.le_refl (n + 2)) hle) ⟨m + 2, hf⟩
      · exact h (m + 2) (Nat.le_add_left 2 m)
          (by rw [hf]; exact Nat.mul_le_mul hle (Nat.le_refl (m + 2)))
          ⟨n + 2, by rw [hf]; exact Nat.mul_comm (n + 2) (m + 2)⟩

end E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
