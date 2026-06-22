import E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity
import E213.Lib.Math.Algebra.Linalg213.InversionsAppend
import E213.Meta.Nat.NatDiv213

/-!
# CharacterOrthogonality — the order-2 character sums to zero (∅-axiom)

The load-bearing Fourier fact for the **quadratic** character: summed over a full
orbit of the cyclic group `⟨g⟩` (the units mod a prime `p`), the order-2
character vanishes,

> `Σ_{k=0}^{p-2} χ(g^k) = 0`,

where `χ(g^k) = (−1)^k` is the quadratic character read as the parity of the
discrete logarithm (`DiscreteLogParity.qr_pow_iff_even_exp`: `g^k` is a quadratic
residue ⟺ `2 ∣ k`).  This is the order-2 instance of the general
`Σ_x χ(x) = 0`: the two `2`-nd roots of unity are `±1`, and the sum of `(−1)^k`
over a complete period `k ∈ [0, 2m)` telescopes pairwise to `0`
(`altSign (2j) + altSign (2j+1) = 1 + (−1) = 0`).

This is exactly the **root-of-unity telescoping sum** that
`research-notes/decomposition/practice/fourier.md` predicts (the order-2 leg of
its open orthogonality target), now cashed in Lean at the Legendre level.

Equivalently (the **count form**), among the exponents `[0, 2m)` exactly `m` are
even and `m` are odd — exactly `(p−1)/2` quadratic residues and `(p−1)/2`
non-residues in the orbit.

  * ★★★ `charSumExp_eq_zero`        — `Σ_{k<2m} (−1)^k = 0`.
  * ★★★ `altSign_eq_one_iff_even`   — `(−1)^k = 1 ⟺ 2 ∣ k` (the sign is the parity bit).
  * ★★★★ `quadratic_orthogonality`  — `Σ_{k<2m} (−1)^k = 0`, with each `(−1)^k`
    certified as the quadratic character `χ(g^k)` via `qr_pow_iff_even_exp`.
  * ★★★ `qr_count_eq_nonqr_count`   — `#even = #odd = m` over `[0, 2m)`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CharacterOrthogonality

open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add)
open E213.Lib.Math.Algebra.Linalg213.InversionsAppend (altSign_double)
open E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity (qr_pow_iff_even_exp)
open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP)
open E213.Meta.Int213 (add_neg_cancel int_ne_neg_self)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (cases_lt_two)
open E213.Meta.Nat.NatDiv213 (two_cancel_lt mul_mod_self_pure)
open E213.Meta.Nat.PureNat (add_left_cancel)
open E213.Meta.Nat.AddMod213 (add_mod_gen)

/-! ## §0 — `2` does not divide an odd number -/

/-- `¬ 2 ∣ (2j+1)`: an odd number is not even.  If `2j+1 = 2c` then cancelling
    `2j` (`c > j`, so `c = j + e` with `e ≥ 1`) forces `1 = 2e ≥ 2`, impossible. -/
theorem two_not_dvd_succ_two_mul (j : Nat) : ¬ 2 ∣ (2 * j + 1) := by
  intro ⟨c, hc⟩
  -- 2*j + 1 = 2*c, so c > j: write c = j + e, get 1 = 2*e
  have hjc : 2 * j < 2 * c := by rw [← hc]; exact Nat.lt_succ_self (2 * j)
  have hjlt : j < c := two_cancel_lt j c hjc
  obtain ⟨e, he⟩ := Nat.le.dest (Nat.le_of_lt hjlt)
  -- he : j + e = c, with e ≥ 1
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hp
    · exfalso; rw [h0, Nat.add_zero] at he; exact Nat.lt_irrefl j (he ▸ hjlt)
    · exact hp
  -- 2*j + 1 = 2*(j+e) = 2*j + 2*e, cancel 2*j ⟹ 1 = 2*e
  have : 2 * j + 1 = 2 * j + 2 * e := by
    rw [hc, ← he, Nat.mul_add]
  have h1 : 1 = 2 * e := add_left_cancel this
  have h2 : 2 * 1 ≤ 2 * e := Nat.mul_le_mul_left 2 he1
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-! ## §1 — the alternating sign at even / odd exponents -/

/-- `altSign (k+1) = − altSign k` (definitional). -/
theorem altSign_succ (k : Nat) : altSign (k + 1) = - altSign k := rfl

/-- `altSign (2j) = 1` (an even power). -/
theorem altSign_two_mul (j : Nat) : altSign (2 * j) = 1 := by
  rw [Nat.two_mul]; exact altSign_double j

/-- `altSign (2j+1) = −1` (an odd power). -/
theorem altSign_two_mul_succ (j : Nat) : altSign (2 * j + 1) = -1 := by
  rw [altSign_succ, altSign_two_mul j]

/-- ★★★ **`(−1)^k = 1 ⟺ 2 ∣ k`** — the alternating sign is the parity bit of the
    exponent.  Split `k = 2·(k/2) + k%2` with `k%2 ∈ {0,1}`: the even branch gives
    `altSign k = 1`, the odd branch `altSign k = −1 ≠ 1`. -/
theorem altSign_eq_one_iff_even (k : Nat) : altSign k = 1 ↔ 2 ∣ k := by
  have hdm : 2 * (k / 2) + k % 2 = k := div_add_mod k 2
  have hr : k % 2 < 2 := Nat.mod_lt k (by decide)
  rcases cases_lt_two hr with hr0 | hr1
  · -- even: k = 2*(k/2)
    have hk : k = 2 * (k / 2) := by rw [hr0, Nat.add_zero] at hdm; exact hdm.symm
    constructor
    · intro _; exact ⟨k / 2, hk⟩
    · intro _; rw [hk]; exact altSign_two_mul (k / 2)
  · -- odd: k = 2*(k/2) + 1
    have hk : k = 2 * (k / 2) + 1 := by rw [hr1] at hdm; exact hdm.symm
    constructor
    · intro h
      exfalso
      rw [hk, altSign_two_mul_succ] at h
      -- h : (-1 : Int) = 1, contradiction
      exact int_ne_neg_self (by decide : (1 : Int) ≠ 0) h.symm
    · intro hd
      exfalso
      rw [hk] at hd
      exact two_not_dvd_succ_two_mul (k / 2) hd

/-! ## §2 — the character sum over a full period is zero -/

/-- A consecutive pair cancels: `altSign (2j) + altSign (2j+1) = 0`. -/
theorem altSign_pair (j : Nat) : altSign (2 * j) + altSign (2 * j + 1) = 0 := by
  rw [altSign_succ (2 * j)]; exact add_neg_cancel (altSign (2 * j))

/-- The character sum over a full period `k ∈ [0, 2m)`: `Σ_{k=0}^{2m-1} (−1)^k`,
    accumulated two terms (`+1, −1`) at a time. -/
def charSumExp : Nat → Int
  | 0     => 0
  | m + 1 => charSumExp m + (altSign (2 * m) + altSign (2 * m + 1))

/-- ★★★ **The order-2 character sums to zero over a full period.**
    `Σ_{k=0}^{2m-1} (−1)^k = 0` — every consecutive `+1, −1` pair cancels. -/
theorem charSumExp_eq_zero : ∀ m, charSumExp m = 0
  | 0     => rfl
  | m + 1 => by
    show charSumExp m + (altSign (2 * m) + altSign (2 * m + 1)) = 0
    rw [charSumExp_eq_zero m, altSign_pair m, Int.add_zero]

/-! ## §3 — orthogonality with the character read as the discrete-log parity -/

/-- ★★★★ **Quadratic-character orthogonality (Legendre level).**

    For an odd prime `p` (`2m = p − 1`, `m ≥ 1`) with primitive root `g`, the
    quadratic character summed over the full orbit `{g^0, …, g^{p−2}}` vanishes:

      `Σ_{k=0}^{p−2} χ(g^k) = Σ_{k<2m} (−1)^k = 0`.

    The second conjunct *certifies the summand is the character*: for every
    exponent `k`, `altSign k = +1 ⟺ g^k is a quadratic residue` — combining
    `altSign_eq_one_iff_even` (`(−1)^k = 1 ⟺ 2 ∣ k`) with `qr_pow_iff_even_exp`
    (`g^k` is a QR ⟺ `2 ∣ k`).  So the vanishing sum is the sum of the Legendre
    symbol over the units, and it is zero. -/
theorem quadratic_orthogonality (p m g : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m)
    (hg1 : 1 ≤ g) (hgle : g ≤ p - 1) (hord : ordModP g p = p - 1) :
    charSumExp m = 0 ∧
      (∀ k, altSign k = 1 ↔ (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = g ^ k % p)) := by
  refine ⟨charSumExp_eq_zero m, fun k => ?_⟩
  exact (altSign_eq_one_iff_even k).trans
    (qr_pow_iff_even_exp p m g hp hpr h2m hm1 hg1 hgle hord k).symm

/-! ## §4 — the count form: `#even = #odd = m` over `[0, 2m)`

The parity test is a **Bool** (`n % 2 == 0`), not a `Decidable (2 ∣ n)` instance —
the latter pulls `propext` into the count's normal form.  `evenInd n` is the
count-Lens parity bit as a `Nat` (`1` even, `0` odd). -/

/-- Even-indicator (∅-axiom Bool readout): `1` if `n` even, `0` if odd. -/
def evenInd (n : Nat) : Nat := if n % 2 == 0 then 1 else 0

/-- Odd-indicator: `0` if `n` even, `1` if odd. -/
def oddInd (n : Nat) : Nat := if n % 2 == 0 then 0 else 1

theorem evenInd_two_mul (m : Nat) : evenInd (2 * m) = 1 := by
  show (if (2 * m) % 2 == 0 then 1 else 0) = 1
  rw [mul_mod_self_pure 2 m]; rfl

theorem evenInd_two_mul_succ (m : Nat) : evenInd (2 * m + 1) = 0 := by
  show (if (2 * m + 1) % 2 == 0 then 1 else 0) = 0
  rw [add_mod_gen (2 * m) 1 2, mul_mod_self_pure 2 m, Nat.zero_add]; rfl

theorem oddInd_two_mul (m : Nat) : oddInd (2 * m) = 0 := by
  show (if (2 * m) % 2 == 0 then 0 else 1) = 0
  rw [mul_mod_self_pure 2 m]; rfl

theorem oddInd_two_mul_succ (m : Nat) : oddInd (2 * m + 1) = 1 := by
  show (if (2 * m + 1) % 2 == 0 then 0 else 1) = 1
  rw [add_mod_gen (2 * m) 1 2, mul_mod_self_pure 2 m, Nat.zero_add]; rfl

/-- `#{k < n : k even}` — the count of even exponents below `n`. -/
def evenCount : Nat → Nat
  | 0     => 0
  | n + 1 => evenCount n + evenInd n

/-- `#{k < n : k odd}` — the count of odd exponents below `n`. -/
def oddCount : Nat → Nat
  | 0     => 0
  | n + 1 => oddCount n + oddInd n

/-- Over a full period `[0, 2m)` there are exactly `m` even exponents:
    each pair `(2j, 2j+1)` contributes one. -/
theorem evenCount_two_mul : ∀ m, evenCount (2 * m) = m
  | 0     => rfl
  | m + 1 => by
    have hstep : 2 * (m + 1) = (2 * m + 1) + 1 := by rw [Nat.mul_succ]
    rw [hstep]
    show evenCount (2 * m + 1) + evenInd (2 * m + 1) = m + 1
    rw [evenInd_two_mul_succ m, Nat.add_zero]
    show evenCount (2 * m) + evenInd (2 * m) = m + 1
    rw [evenInd_two_mul m, evenCount_two_mul m]

/-- Over a full period `[0, 2m)` there are exactly `m` odd exponents. -/
theorem oddCount_two_mul : ∀ m, oddCount (2 * m) = m
  | 0     => rfl
  | m + 1 => by
    have hstep : 2 * (m + 1) = (2 * m + 1) + 1 := by rw [Nat.mul_succ]
    rw [hstep]
    show oddCount (2 * m + 1) + oddInd (2 * m + 1) = m + 1
    rw [oddInd_two_mul_succ m]
    show (oddCount (2 * m) + oddInd (2 * m)) + 1 = m + 1
    rw [oddInd_two_mul m, Nat.add_zero, oddCount_two_mul m]

/-- ★★★ **Count form of quadratic-character orthogonality.**  Over the orbit
    `{g^0, …, g^{2m−1}}` there are exactly `m` quadratic residues (even exponents)
    and exactly `m` non-residues (odd exponents): `#even = #odd = m`.  This is the
    `Σ χ = 0` fact restated as `(p−1)/2` residues and `(p−1)/2` non-residues. -/
theorem qr_count_eq_nonqr_count (m : Nat) :
    evenCount (2 * m) = m ∧ oddCount (2 * m) = m ∧
      evenCount (2 * m) = oddCount (2 * m) :=
  ⟨evenCount_two_mul m, oddCount_two_mul m,
    (evenCount_two_mul m).trans (oddCount_two_mul m).symm⟩

end E213.Lib.Math.NumberTheory.ModArith.CharacterOrthogonality
