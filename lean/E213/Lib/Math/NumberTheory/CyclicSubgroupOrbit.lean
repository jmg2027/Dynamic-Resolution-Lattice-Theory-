import E213.Lib.Math.NumberTheory.MultiplicativeOrder
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

/-!
# The cyclic subgroup `⟨a⟩ mod n` is the explicit finite orbit (∅-axiom)

**Forcing (vein A).**  Classically `⟨a⟩` is an abstract cyclic *subgroup* of the
quotient group `(ℤ/n)*`, and "`|⟨a⟩|` divides `|(ℤ/n)*| = φ(n)`" is Lagrange's
theorem via coset counting.  With **no quotient / no abstract group**, `⟨a⟩` is
the **concrete finite orbit** `{ a^k % n : k < ord n a }`: the powers are
pairwise distinct below the order (`pow_inj_below_ord`, by `ord_min` after
cancelling the unit `a^i`), they cycle with period `ord n a` (`pow_period`), the
set is closed under `·` mod `n` by folding the exponent back below `ord`
(`orbit_mul_closed`), and the divisibility is the **computed**
`ord n a ∣ φ(n)` (`cyclic_lagrange`, i.e. Euler + minimality via
`ord_dvd_of_pow_one`), **not** a coset count.

One line: *the cyclic subgroup is the concrete orbit; Lagrange (cyclic case) is
the order-divides-totient computation.*

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.CyclicSubgroupOrbit

open E213.Tactic.NatHelper (gcd213 add_sub_of_le)
open E213.Lib.Math.NumberTheory.MultiplicativeOrder
  (ord ord_pos ord_min pow_ord_eq_one ord_dvd_of_pow_one ord_dvd_totient)
open E213.Lib.Math.NumberTheory.EulerTotient (totient)
open E213.Lib.Math.NumberTheory.EulerTheorem (cancel_unit)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_pow_left)
open E213.Meta.Nat.MulMod213 (mul_mod_pure mul_mod_left_pure mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (mod_mod div_add_mod)

/-! ## §1 — periodicity: the powers cycle with period `ord` -/

/-- ★★★ **Periodicity**: `a^(k + ord) ≡ a^k (mod n)`.  The powers cycle with
    period `ord n a` (`a^(k+ord) = a^k · a^ord ≡ a^k · 1`). -/
theorem pow_period (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) (k : Nat) :
    a ^ (k + ord n a) % n = a ^ k % n := by
  rw [pow_add_pure a k (ord n a)]
  -- (a^k * a^ord) % n  with  a^ord ≡ 1
  calc a ^ k * a ^ ord n a % n
      = (a ^ k % n * (a ^ ord n a % n)) % n := mul_mod_pure _ _ n
    _ = (a ^ k % n * (1 % n)) % n := by rw [pow_ord_eq_one n a hn hcop]
    _ = (a ^ k % n * 1) % n := by rw [Nat.mod_eq_of_lt hn]
    _ = a ^ k % n % n := by rw [Nat.mul_one]
    _ = a ^ k % n := mod_mod _ _

/-! ## §2 — distinct powers below the order -/

/-- Helper: `a^i` is a unit mod `n` whenever `a` is. -/
theorem pow_coprime (n a : Nat) (hcop : gcd213 a n = 1) (i : Nat) :
    gcd213 (a ^ i) n = 1 := coprime_pow_left hcop i

/-- Ordered injectivity: `i ≤ j < ord`, `a^i ≡ a^j` ⟹ `i = j`.
    `a^j = a^i · a^(j−i)`, cancel the unit `a^i` to get `a^(j−i) ≡ 1` with
    `j−i < ord`, so `ord_min` forces `j−i = 0`. -/
theorem pow_inj_le (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1)
    {i j : Nat} (hij : i ≤ j) (hj : j < ord n a)
    (h : a ^ i % n = a ^ j % n) : i = j := by
  -- a^j = a^i * a^(j-i)
  have hsplit : a ^ j = a ^ i * a ^ (j - i) := by
    rw [← pow_add_pure a i (j - i), add_sub_of_le hij]
  -- cancel the unit a^i:  (a^i * a^(j-i)) % n = (a^i * 1) % n
  have hPunit : gcd213 (a ^ i) n = 1 := pow_coprime n a hcop i
  have hcform : (a ^ i * a ^ (j - i)) % n = (a ^ i * 1) % n := by
    rw [Nat.mul_one, ← hsplit]
    exact h.symm
  have hcancel : a ^ (j - i) % n = 1 :=
    cancel_unit hn hPunit hcform hn
  -- a^(j-i) ≡ 1 % n, with j-i < ord ⟹ minimality forces j-i = 0
  have h1mod : a ^ (j - i) % n = 1 % n := by
    rw [hcancel, Nat.mod_eq_of_lt hn]
  have hji_lt : j - i < ord n a := Nat.lt_of_le_of_lt (Nat.sub_le j i) hj
  have hji0 : j - i = 0 := by
    rcases Nat.eq_zero_or_pos (j - i) with h0 | hpos
    · exact h0
    · exact absurd h1mod (ord_min n a hn hcop (j - i) hpos hji_lt)
  -- j - i = 0 with i ≤ j ⟹ i = j
  exact Nat.le_antisymm hij (Nat.le_of_sub_eq_zero hji0)

/-- ★★★ **Distinct powers below the order**: for `i, j < ord n a`,
    `a^i ≡ a^j (mod n) ⟹ i = j`.  WLOG `i ≤ j`, then `pow_inj_le`. -/
theorem pow_inj_below_ord (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1)
    {i j : Nat} (hi : i < ord n a) (hj : j < ord n a)
    (h : a ^ i % n = a ^ j % n) : i = j := by
  rcases Nat.le_total i j with hij | hji
  · exact pow_inj_le n a hn hcop hij hj h
  · exact (pow_inj_le n a hn hcop hji hi h.symm).symm

/-! ## §3 — the orbit predicate; it is a subgroup -/

/-- The cyclic subgroup `⟨a⟩ mod n` as the **concrete finite orbit**:
    `orbit n a y` holds iff `y = a^k % n` for some exponent `k < ord n a`. -/
def orbit (n a y : Nat) : Prop := ∃ k, k < ord n a ∧ y = a ^ k % n

/-- The identity `1 % n` is in the orbit (`k = 0`, `a^0 = 1`). -/
theorem orbit_one (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    orbit n a (1 % n) :=
  ⟨0, ord_pos n a hn hcop, by rw [Nat.pow_zero]⟩

/-- Reduce an exponent below the order while preserving `a^k % n`:
    `a^k % n = a^(k % ord) % n`.  (Fold `pow_period` along division.) -/
theorem pow_mod_ord (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    ∀ k, a ^ k % n = a ^ (k % ord n a) % n := by
  have hop : 1 ≤ ord n a := ord_pos n a hn hcop
  -- strong-induction-free: induct on the quotient via fuel = k
  -- prove the auxiliary: for all q r, a^(ord*q + r) % n = a^r % n
  have haux : ∀ q r, a ^ (ord n a * q + r) % n = a ^ r % n := by
    intro q
    induction q with
    | zero => intro r; rw [Nat.mul_zero, Nat.zero_add]
    | succ q ih =>
      intro r
      -- ord*(q+1) + r = (ord*q + r) + ord
      have he : ord n a * (q + 1) + r = (ord n a * q + r) + ord n a := by
        rw [Nat.mul_succ]
        rw [Nat.add_right_comm (ord n a * q) (ord n a) r]
      rw [he, pow_period n a hn hcop (ord n a * q + r), ih r]
  intro k
  have hdm : ord n a * (k / ord n a) + k % ord n a = k := div_add_mod k (ord n a)
  have := haux (k / ord n a) (k % ord n a)
  rw [hdm] at this
  exact this

/-- ★★ **The orbit is closed under multiplication mod `n`** — it IS a subgroup.
    `a^i · a^j = a^(i+j)`; fold the exponent `i+j` back below `ord`. -/
theorem orbit_mul_closed (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1)
    {x y : Nat} (hx : orbit n a x) (hy : orbit n a y) :
    orbit n a ((x * y) % n) := by
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  -- (a^i % n * (a^j % n)) % n = a^(i+j) % n = a^((i+j) % ord) % n
  refine ⟨(i + j) % ord n a, Nat.mod_lt _ (ord_pos n a hn hcop), ?_⟩
  rw [← mul_mod_pure (a ^ i) (a ^ j) n, ← pow_add_pure a i j]
  exact pow_mod_ord n a hn hcop (i + j)

/-! ## §4 — Lagrange (cyclic case) = the order-divides-totient computation -/

/-- ★★ **Lagrange's theorem, cyclic case (on representatives).**

    `ord n a ∣ totient n` — the cyclic subgroup `⟨a⟩` has order `ord n a`, and
    that order divides the group order `|(ℤ/n)*| = φ(n)`.

    The point: with no quotient group, this is **not** coset counting.  It is
    the explicit `ord_dvd_of_pow_one` applied to Euler's `a^φ(n) ≡ 1` — i.e.
    `ord` divides `φ(n)` because the order divides *every* exponent that fixes
    `a`, and Euler supplies one such exponent.  Re-exported from
    `MultiplicativeOrder.ord_dvd_totient` with the cyclic-subgroup reading. -/
theorem cyclic_lagrange (n a : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    ord n a ∣ totient n := ord_dvd_totient n a hn hcop

/-! ## §5 — concrete smokes -/

/-- Smoke: `n = 7, a = 3` — `ord = 6`, orbit `= {3,2,6,4,5,1}` all distinct,
    `|orbit| = 6 = φ(7)`. -/
theorem smoke_ord_3_7 : ord 7 3 = 6 := by decide

/-- The six powers `3^0..3^5 mod 7` are exactly `1,3,2,6,4,5` (pairwise distinct). -/
theorem smoke_orbit_3_7 :
    (3 : Nat) ^ 0 % 7 = 1 ∧ (3 : Nat) ^ 1 % 7 = 3 ∧ (3 : Nat) ^ 2 % 7 = 2 ∧
    (3 : Nat) ^ 3 % 7 = 6 ∧ (3 : Nat) ^ 4 % 7 = 4 ∧ (3 : Nat) ^ 5 % 7 = 5 := by
  decide

/-- Smoke: `|orbit| = ord = φ(7) = 6`. -/
theorem smoke_card_3_7 : ord 7 3 = totient 7 := by decide

/-- Smoke: periodicity at `n=7,a=3`, `k=2`: `3^(2+6) ≡ 3^2 (mod 7)`. -/
theorem smoke_period_3_7 : (3 : Nat) ^ (2 + 6) % 7 = (3 : Nat) ^ 2 % 7 := by decide

/-- Smoke: `n = 5, a = 2` — `ord = 4 = φ(5)`. -/
theorem smoke_ord_2_5 : ord 5 2 = 4 ∧ ord 5 2 = totient 5 := by decide

end E213.Lib.Math.NumberTheory.CyclicSubgroupOrbit
