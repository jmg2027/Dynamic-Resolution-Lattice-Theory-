import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.ModPow213
import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213

/-!
# Multiplicative order divides `φ(n)` for composite `n` (∅-axiom)

The corpus order theory (`ModArith/MulOrder`) is **prime-specific**: its
existence-of-the-order step is fed by Fermat (`a^(p−1) ≡ 1`) and it carries the
primality predicate `∀ d, d∣p → d=1∨d=p` throughout.  Here we redo it for an
**arbitrary modulus** `1 < n` and a unit `gcd(a,n)=1`, with the hit exponent
supplied by **Euler's theorem** (`a^φ(n) ≡ 1 (mod n)`,
`EulerTheorem.euler_theorem`).  The order-divides-everything-that-fixes-`a`
argument (division with remainder + minimality) carries over unchanged.

  * `ord n a` — least `d ∈ [1, n]` with `aᵈ % n = 1 % n` (search fuel `= n`).
  * `pow_ord_eq_one`, `ord_pos` — the found `d` works and is positive.
  * `ord_min` — no smaller positive exponent works.
  * ★★★ `ord_dvd_of_pow_one` — `aᵏ ≡ 1 ⟹ ord ∣ k`.
  * ★★★ `ord_dvd_totient` — `ord n a ∣ totient n`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MultiplicativeOrder

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTotient (totient coprimeInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.EulerTheorem (euler_theorem)
open E213.Meta.Nat.Gcd213 (gcd213_one_left)
open E213.Meta.Nat.AddMod213 (div_add_mod mod_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §0 — `totient` bounds (positive, `≤ n`) -/

/-- The head term bounds the sum: `f 0 ≤ sumTo n f` for `0 < n`. -/
theorem head_le_sumTo (f : Nat → Nat) : ∀ {n}, 0 < n → f 0 ≤ sumTo n f
  | 0,     h => absurd h (Nat.lt_irrefl 0)
  | n + 1, _ => by
    show f 0 ≤ sumTo n f + f n
    cases Nat.eq_zero_or_pos n with
    | inl hz => subst hz; show f 0 ≤ 0 + f 0; rw [Nat.zero_add]; exact Nat.le_refl _
    | inr hp => exact Nat.le_trans (head_le_sumTo f hp) (Nat.le_add_right _ _)

/-- Each term is `≤ 1`, so `sumTo n f ≤ n` (here `f k = coprimeInd k n`). -/
theorem sumTo_le_self (f : Nat → Nat) (hf : ∀ k, f k ≤ 1) : ∀ n, sumTo n f ≤ n
  | 0     => Nat.le_refl 0
  | n + 1 => by
    show sumTo n f + f n ≤ n + 1
    exact Nat.add_le_add (sumTo_le_self f hf n) (hf n)

/-- `coprimeInd k n ≤ 1` (it is a `Bool.toNat`). -/
theorem coprimeInd_le_one (k n : Nat) : coprimeInd k n ≤ 1 := by
  show (gcd213 (k + 1) n == 1).toNat ≤ 1
  cases (gcd213 (k + 1) n == 1) <;> decide

/-- `coprimeInd 0 n = 1` (gcd(1,n)=1 always). -/
theorem coprimeInd_zero (n : Nat) : coprimeInd 0 n = 1 := by
  show (gcd213 (0 + 1) n == 1).toNat = 1
  rw [Nat.zero_add, gcd213_one_left n]; rfl

/-- `1 ≤ totient n` for `0 < n`. -/
theorem totient_pos {n : Nat} (hn : 0 < n) : 1 ≤ totient n := by
  show 1 ≤ sumTo n (fun k => coprimeInd k n)
  have h := head_le_sumTo (fun k => coprimeInd k n) hn
  rw [show (fun k => coprimeInd k n) 0 = coprimeInd 0 n from rfl, coprimeInd_zero n] at h
  exact h

/-- `totient n ≤ n`. -/
theorem totient_le_self (n : Nat) : totient n ≤ n :=
  sumTo_le_self (fun k => coprimeInd k n) (fun k => coprimeInd_le_one k n) n

/-! ## §1 — the order search (fuel-bounded linear scan) -/

/-- Search upward from `start` for the least exponent with `aᵏ % n = 1 % n`. -/
def findOrd (a n : Nat) : Nat → Nat → Option Nat
  | _, 0        => none
  | k, fuel + 1 => if a ^ k % n = 1 % n then some k else findOrd a n (k + 1) fuel

/-- A found order satisfies the congruence and is `≥` the search start. -/
theorem findOrd_some (a n : Nat) : ∀ (fuel start k : Nat),
    findOrd a n start fuel = some k → a ^ k % n = 1 % n ∧ start ≤ k
  | 0,        _,     _, h => Option.noConfusion h
  | fuel + 1, start, k, h => by
    rw [findOrd] at h
    by_cases hc : a ^ start % n = 1 % n
    · rw [if_pos hc] at h
      have : start = k := Option.some.inj h
      subst this; exact ⟨hc, Nat.le_refl _⟩
    · rw [if_neg hc] at h
      obtain ⟨h1, h2⟩ := findOrd_some a n fuel (start + 1) k h
      exact ⟨h1, Nat.le_trans (Nat.le_succ start) h2⟩

/-- A found order is minimal: nothing in `[start, k)` satisfies the congruence. -/
theorem findOrd_min (a n : Nat) : ∀ (fuel start k : Nat),
    findOrd a n start fuel = some k → ∀ j, start ≤ j → j < k → a ^ j % n ≠ 1 % n
  | 0,        _,     _, h => Option.noConfusion h
  | fuel + 1, start, k, h => by
    rw [findOrd] at h
    by_cases hc : a ^ start % n = 1 % n
    · rw [if_pos hc] at h
      have hsk : start = k := Option.some.inj h
      intro j hsj hjk
      rw [← hsk] at hjk
      exact absurd hjk (Nat.not_lt.mpr hsj)
    · rw [if_neg hc] at h
      intro j hsj hjk
      rcases Nat.lt_or_eq_of_le hsj with hlt | heq
      · exact findOrd_min a n fuel (start + 1) k h j hlt hjk
      · rw [← heq]; exact hc

/-- The search succeeds within `fuel` whenever some exponent in `[start, start+fuel)` works. -/
theorem findOrd_found (a n : Nat) : ∀ (fuel start t : Nat),
    start ≤ t → t < start + fuel → a ^ t % n = 1 % n → ∃ k, findOrd a n start fuel = some k
  | 0,        _,     t, hst, hlt, _  => by
    rw [Nat.add_zero] at hlt; exact absurd hlt (Nat.not_lt.mpr hst)
  | fuel + 1, start, t, hst, hlt, ht => by
    rw [findOrd]
    by_cases hc : a ^ start % n = 1 % n
    · exact ⟨start, by rw [if_pos hc]⟩
    · rw [if_neg hc]
      have hst' : start + 1 ≤ t := by
        rcases Nat.lt_or_eq_of_le hst with hlt2 | heq
        · exact hlt2
        · exact absurd (heq ▸ ht) hc
      exact findOrd_found a n fuel (start + 1) t hst' (by
        rw [Nat.succ_add]; exact hlt) ht

/-! ## §2 — `ord` and its defining laws -/

/-- The multiplicative order of `a` mod `n` (least positive exponent with
    `aᵏ ≡ 1 (mod n)`); `0` if the search finds none. -/
def ord (n a : Nat) : Nat := (findOrd a n 1 n).getD 0

/-- For `1 < n` and a unit `a`, the search succeeds: Euler supplies the hit
    exponent `φ(n) ∈ [1, n]`. -/
theorem ord_found (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    ∃ k, findOrd a n 1 n = some k := by
  have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have heu : a ^ (totient n) % n = 1 % n := euler_theorem a n hn hcop
  have htpos : 1 ≤ totient n := totient_pos hnpos
  have htle : totient n ≤ n := totient_le_self n
  have hlt : totient n < 1 + n :=
    Nat.lt_of_le_of_lt htle (by rw [Nat.add_comm]; exact Nat.lt_succ_self n)
  exact findOrd_found a n n 1 (totient n) htpos hlt heu

/-- ★★ **The order is a valid period**: `aᵒʳᵈ ≡ 1 (mod n)`. -/
theorem pow_ord_eq_one (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    a ^ (ord n a) % n = 1 % n := by
  obtain ⟨k, hk⟩ := ord_found n a hn hcop
  have hord : ord n a = k := congrArg (·.getD 0) hk
  rw [hord]; exact (findOrd_some a n n 1 k hk).1

/-- `1 ≤ ord n a`. -/
theorem ord_pos (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    1 ≤ ord n a := by
  obtain ⟨k, hk⟩ := ord_found n a hn hcop
  have hord : ord n a = k := congrArg (·.getD 0) hk
  rw [hord]; exact (findOrd_some a n n 1 k hk).2

/-- Minimality: no positive exponent below the order satisfies the congruence. -/
theorem ord_min (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    ∀ j, 1 ≤ j → j < ord n a → a ^ j % n ≠ 1 % n := by
  obtain ⟨k, hk⟩ := ord_found n a hn hcop
  have hord : ord n a = k := congrArg (·.getD 0) hk
  rw [hord]; exact findOrd_min a n n 1 k hk

/-! ## §3 — ★★★ `aᵏ ≡ 1 ⟹ ord ∣ k` -/

/-- `a^(ord·q + r) ≡ aʳ (mod n)` — the `a^ord ≡ 1` collapse. -/
theorem pow_split_eq (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) (q r : Nat) :
    a ^ (ord n a * q + r) % n = a ^ r % n := by
  rw [pow_add_pure a (ord n a * q) r, pow_mul_loc a (ord n a) q]
  -- ((a^ord)^q * a^r) % n, with (a^ord)^q ≡ 1
  have hbase : (a ^ ord n a) ^ q % n = 1 := by
    rw [pow_mod_base (a ^ ord n a) n q, pow_ord_eq_one n a hn hcop,
        Nat.mod_eq_of_lt hn]
    show 1 ^ q % n = 1
    rw [Nat.one_pow]; exact Nat.mod_eq_of_lt hn
  calc (a ^ ord n a) ^ q * a ^ r % n
      = ((a ^ ord n a) ^ q % n * (a ^ r % n)) % n := mul_mod_pure _ _ n
    _ = (1 * (a ^ r % n)) % n := by rw [hbase]
    _ = a ^ r % n := by rw [Nat.one_mul, mod_mod]

/-- ★★★ **`aᵏ ≡ 1 ⟹ ord ∣ k`** — the order divides every exponent that fixes `a`.
    By `k = ord·q + r` (`r < ord`): `aᵏ ≡ aʳ`, so `aʳ ≡ 1` with `r < ord` forces
    `r = 0` (minimality). -/
theorem ord_dvd_of_pow_one (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1)
    {k : Nat} (hk : 1 ≤ k) (h : a ^ k % n = 1 % n) : ord n a ∣ k := by
  have hop : 1 ≤ ord n a := ord_pos n a hn hcop
  have hdm : ord n a * (k / ord n a) + k % ord n a = k := div_add_mod k (ord n a)
  have hr : a ^ (k % ord n a) % n = 1 % n := by
    have hsp := pow_split_eq n a hn hcop (k / ord n a) (k % ord n a)
    rw [hdm] at hsp; rw [← hsp]; exact h
  -- r = k % ord < ord, and a^r ≡ 1 ⟹ r = 0 (minimality)
  have hrlt : k % ord n a < ord n a :=
    Nat.mod_lt k (Nat.lt_of_lt_of_le Nat.zero_lt_one hop)
  have hr0 : k % ord n a = 0 := by
    rcases Nat.eq_zero_or_pos (k % ord n a) with h0 | hpos
    · exact h0
    · exact absurd hr (ord_min n a hn hcop (k % ord n a) hpos hrlt)
  have hk_eq : ord n a * (k / ord n a) = k := by
    rw [hr0, Nat.add_zero] at hdm; exact hdm
  exact ⟨k / ord n a, hk_eq.symm⟩

/-! ## §4 — ★★★ `ord ∣ φ(n)` and corollaries -/

/-- ★★★ **`ord n a ∣ totient n`** — the multiplicative order divides `φ(n)`,
    for *any* modulus `1 < n` (composite or prime).  Apply `ord_dvd_of_pow_one`
    to Euler's `a^φ(n) ≡ 1`. -/
theorem ord_dvd_totient (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    ord n a ∣ totient n :=
  ord_dvd_of_pow_one n a hn hcop (totient_pos (Nat.lt_trans Nat.zero_lt_one hn))
    (euler_theorem a n hn hcop)

/-- `ord n a ≤ totient n` (the order divides `φ(n)`, which is positive). -/
theorem ord_le_totient (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    ord n a ≤ totient n := by
  have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  exact le_of_dvd_pos (ord n a) (totient n) (totient_pos hnpos)
    (ord_dvd_totient n a hn hcop)

/-! ## §5 — smokes -/

/-- Smoke: φ(10)=4, ord₁₀(3)=4, and 4 ∣ 4. -/
theorem smoke_ord_3_10 : ord 10 3 ∣ totient 10 :=
  ord_dvd_totient 10 3 (by decide) (by decide)

/-- Smoke: the concrete order value `ord₁₀(3) = 4`. -/
theorem smoke_ord_3_10_val : ord 10 3 = 4 := by decide

/-- Smoke: φ(9)=6, ord₉(2)=6, 6 ∣ 6. -/
theorem smoke_ord_2_9 : ord 9 2 ∣ totient 9 :=
  ord_dvd_totient 9 2 (by decide) (by decide)

theorem smoke_ord_2_9_val : ord 9 2 = 6 := by decide

/-- Smoke: composite `n = 8`, φ(8)=4, ord₈(3)=2, 2 ∣ 4. -/
theorem smoke_ord_3_8 : ord 8 3 ∣ totient 8 :=
  ord_dvd_totient 8 3 (by decide) (by decide)

theorem smoke_ord_3_8_val : ord 8 3 = 2 := by decide

/-- Smoke: prime case recovered (`n = 7`), φ(7)=6, ord₇(3)=6, 6 ∣ 6. -/
theorem smoke_ord_3_7 : ord 7 3 ∣ totient 7 :=
  ord_dvd_totient 7 3 (by decide) (by decide)

end E213.Lib.Math.NumberTheory.MultiplicativeOrder
