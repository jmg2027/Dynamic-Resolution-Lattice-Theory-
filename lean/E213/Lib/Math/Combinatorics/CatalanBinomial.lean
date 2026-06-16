import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.NatDiv213

/-!
# Catalan ↔ central-binomial bridge (∅-axiom)

The corpus's `catalan` is a finite lookup table (n = 0..7, sentinel `0` beyond),
while `choose` is the Pascal-recurrence binomial.  This file ties them together
and supplies the **universal** engine the table can only exhibit instance-wise.

  * **`central_binom_recurrence`** (★, all `n`): the central-binomial recurrence
    `(n+1)·C(2n+2, n+1) = 2·(2n+1)·C(2n, n)` — the `choose`-level engine behind
    the Catalan growth law `C_{n+1}/C_n = 2(2n+1)/(n+2)`.  Derived *structurally*
    from the Pascal toolkit (`choose_succ_mul` + symmetry), not by `decide`, so it
    holds for every `n`.
  * **`catalan_central_binom`**: the bridge `(n+1)·catalan n = choose (2n) n`
    across the tabulated range, connecting the two independently-built objects.
  * **`catalan_ratio_cross`**: the cross-multiplied Catalan ratio
    `(n+2)·C_{n+1} = 2(2n+1)·C_n` over the real-table range — the universal
    recurrence instantiated on the `catalan` table.

All ∅-axiom (the `Nat.mul_assoc` propext-landmine is avoided via the NatHelper
PURE twin `mul_assoc`).
-/

namespace E213.Lib.Math.Combinatorics.CatalanBinomial

open E213.Lib.Math.Combinatorics.Catalan (catalan)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_succ_mul choose_symm_sum choose_succ_succ)
open E213.Tactic.NatHelper
  (mul_assoc add_sub_cancel_right gcd213 mul_left_cancel_pos add_left_cancel)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)
open E213.Meta.Nat.Gcd213
  (gcd213_comm gcd213_sub_left gcd213_succ_self coprime_dvd_of_dvd_mul)

/-- Helper: `choose (2n+1) n = choose (2n+1) (n+1)` by symmetry (`n + (n+1) = 2n+1`). -/
theorem choose_symm_2n1 (n : Nat) :
    choose (2 * n + 1) n = choose (2 * n + 1) (n + 1) :=
  choose_symm_sum (2 * n + 1) n (n + 1) (by ring_nat)

/-- Helper: `(n+1) · choose (2n+1) (n+1) = (2n+1) · choose (2n) n`.
    Instance of `choose_succ_mul (2n) n`. -/
theorem central_succ_mul (n : Nat) :
    (n + 1) * choose (2 * n + 1) (n + 1) = (2 * n + 1) * choose (2 * n) n :=
  choose_succ_mul (2 * n) n

/-- ★★ **Universal central-binomial recurrence**:
    `(n+1) · choose (2n+2) (n+1) = 2 · (2n+1) · choose (2n) n`.
    Holds for every `n`; the `choose`-level engine behind the Catalan ratio.
    ∅-axiom (built structurally from the Pascal toolkit). -/
theorem central_binom_recurrence (n : Nat) :
    (n + 1) * choose (2 * n + 2) (n + 1)
      = 2 * (2 * n + 1) * choose (2 * n) n := by
  -- Step 1: choose_succ_mul (2n+1) n :
  --   (n+1) · choose (2n+2) (n+1) = (2n+2) · choose (2n+1) n
  have step1 : (n + 1) * choose (2 * n + 2) (n + 1)
      = (2 * n + 2) * choose (2 * n + 1) n := by
    have h := choose_succ_mul (2 * n + 1) n
    rw [show 2 * n + 1 + 1 = 2 * n + 2 from rfl] at h
    exact h
  -- Step 2: rewrite choose (2n+1) n via symmetry, then central_succ_mul
  rw [step1, choose_symm_2n1 n]
  rw [show 2 * n + 2 = 2 * (n + 1) from by ring_nat]
  rw [mul_assoc 2 (n + 1) (choose (2 * n + 1) (n + 1)), central_succ_mul n,
      ← mul_assoc 2 (2 * n + 1) (choose (2 * n) n)]

/-- ★ **Catalan–central-binomial bridge** at each tabulated `n`:
    `(n+1) · catalan n = choose (2n) n`. -/
theorem catalan_central_binom :
    1 * catalan 0 = choose 0 0
    ∧ 2 * catalan 1 = choose 2 1
    ∧ 3 * catalan 2 = choose 4 2
    ∧ 4 * catalan 3 = choose 6 3
    ∧ 5 * catalan 4 = choose 8 4
    ∧ 6 * catalan 5 = choose 10 5
    ∧ 7 * catalan 6 = choose 12 6
    ∧ 8 * catalan 7 = choose 14 7 := by decide

/-- ★ **Catalan cross-multiplied ratio** `(n+2)·C_{n+1} = 2·(2n+1)·C_n`
    over the range where the table is real (n = 0..5) — the universal
    `central_binom_recurrence` instantiated on the `catalan` table. -/
theorem catalan_ratio_cross :
    2 * catalan 1 = 2 * (2 * 0 + 1) * catalan 0
    ∧ 3 * catalan 2 = 2 * (2 * 1 + 1) * catalan 1
    ∧ 4 * catalan 3 = 2 * (2 * 2 + 1) * catalan 2
    ∧ 5 * catalan 4 = 2 * (2 * 3 + 1) * catalan 3
    ∧ 6 * catalan 5 = 2 * (2 * 4 + 1) * catalan 4
    ∧ 7 * catalan 6 = 2 * (2 * 5 + 1) * catalan 5 := by decide

/-! ## Catalan integrality `(n+1) ∣ C(2n,n)` -/

/-- `gcd213 (n+1) (2n+1) = 1`: consecutive-style coprimality.  Since
    `2n+1 = (n+1) + n`, Euclid's subtraction step reduces `gcd(2n+1, n+1)` to
    `gcd(n, n+1) = 1`. -/
theorem gcd_succ_two_succ (n : Nat) : gcd213 (n + 1) (2 * n + 1) = 1 := by
  have hle : (n + 1) ≤ (2 * n + 1) := by
    rw [show 2 * n + 1 = n + (n + 1) from by ring_nat]
    exact Nat.le_add_left (n + 1) n
  have hsub : (2 * n + 1) - (n + 1) = n := by
    rw [Nat.succ_sub_succ_eq_sub, show 2 * n = n + n from by ring_nat,
        add_sub_cancel_right n n]
  calc gcd213 (n + 1) (2 * n + 1)
      = gcd213 (2 * n + 1) (n + 1) := gcd213_comm (n + 1) (2 * n + 1)
    _ = gcd213 ((2 * n + 1) - (n + 1)) (n + 1) := gcd213_sub_left (2 * n + 1) (n + 1) hle
    _ = gcd213 n (n + 1) := by rw [hsub]
    _ = gcd213 (n + 1) n := gcd213_comm n (n + 1)
    _ = 1 := gcd213_succ_self n

/-- `(n+1) ∣ (2n+1) · choose (2n) n` — from `central_succ_mul` the product is
    `(n+1)·choose(2n+1)(n+1)`, manifestly divisible by `n+1`. -/
theorem succ_dvd_central_mul (n : Nat) :
    (n + 1) ∣ (2 * n + 1) * choose (2 * n) n :=
  ⟨choose (2 * n + 1) (n + 1), (central_succ_mul n).symm⟩

/-- ★★ **Catalan integrality**: `(n+1) ∣ choose (2n) n` — the deep fact behind
    `Cₙ = C(2n,n)/(n+1) ∈ ℕ`.  `n+1 ⊥ 2n+1` (consecutive coprimality) + Euclid's
    lemma applied to `(n+1) ∣ (2n+1)·C(2n,n)`. -/
theorem catalan_integrality (n : Nat) : (n + 1) ∣ choose (2 * n) n :=
  coprime_dvd_of_dvd_mul (gcd_succ_two_succ n) (succ_dvd_central_mul n)

/-! ## The general Catalan number `Cₙ = C(2n,n)/(n+1)` -/

/-- The **general Catalan number** `Cₙ = C(2n,n)/(n+1)`, well-defined as a `Nat`
    (exact division licensed by `catalan_integrality`) — unlike the finite
    `Catalan.catalan` table this is defined for all `n`. -/
def catN (n : Nat) : Nat := choose (2 * n) n / (n + 1)

/-- ★ **Exactness**: `(n+1) · catN n = choose (2n) n` — the division is exact, so
    `catN` recovers the central binomial.  From `catalan_integrality` +
    `mul_div_cancel_left_pure`. -/
theorem succ_mul_catN (n : Nat) : (n + 1) * catN n = choose (2 * n) n := by
  obtain ⟨q, hq⟩ := catalan_integrality n
  have hcat : catN n = q := by
    show choose (2 * n) n / (n + 1) = q
    rw [hq]
    exact mul_div_cancel_left_pure (n + 1) q (Nat.succ_pos n)
  rw [hcat]; exact hq.symm

/-- Table agreement: `catN 0..7 = 1,1,2,5,14,42,132,429`. -/
theorem catN_table :
    catN 0 = 1 ∧ catN 1 = 1 ∧ catN 2 = 2 ∧ catN 3 = 5
    ∧ catN 4 = 14 ∧ catN 5 = 42 ∧ catN 6 = 132 ∧ catN 7 = 429 := by decide

/-- Bridge to the corpus table: `catN n = catalan n` for n = 0..7. -/
theorem catN_eq_catalan :
    catN 0 = catalan 0 ∧ catN 1 = catalan 1 ∧ catN 2 = catalan 2 ∧ catN 3 = catalan 3
    ∧ catN 4 = catalan 4 ∧ catN 5 = catalan 5 ∧ catN 6 = catalan 6
    ∧ catN 7 = catalan 7 := by decide

/-- ★ **`catN` ratio recurrence**: `(n+2)·catN (n+1) = 2·(2n+1)·catN n`.
    From `central_binom_recurrence` + the exactness `succ_mul_catN`, cancelling
    the positive `(n+1)`. -/
theorem succ_mul_catN_recurrence (n : Nat) :
    (n + 2) * catN (n + 1) = 2 * (2 * n + 1) * catN n := by
  have hL : (n + 2) * catN (n + 1) = choose (2 * (n + 1)) (n + 1) := succ_mul_catN (n + 1)
  have hR : (n + 1) * catN n = choose (2 * n) n := succ_mul_catN n
  have key : (n + 1) * ((n + 2) * catN (n + 1))
      = (n + 1) * (2 * (2 * n + 1) * catN n) := by
    rw [hL]
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring_nat]
    rw [central_binom_recurrence n, ← hR]
    ring_nat
  exact mul_left_cancel_pos (Nat.succ_pos n) key

/-- ★ **`catN` recurrence, `4n+2` form**: `(n+2)·catN (n+1) = (4n+2)·catN n`
    (restatement of `succ_mul_catN_recurrence`'s `2·(2n+1)` shape — the bridge to
    the growth bound). -/
theorem succ_mul_catN_recurrence_4np2 (n : Nat) :
    (n + 2) * catN (n + 1) = (4 * n + 2) * catN n := by
  rw [succ_mul_catN_recurrence n]
  rw [show 2 * (2 * n + 1) = 4 * n + 2 from by ring_nat]

/-- ★★ **General Catalan growth bound** `catN (n+1) ≤ 4·catN n`, for **every** `n`.

    The `C_{n+1}/C_n = 2(2n+1)/(n+2) → 4` asymptotic in `≤` form, on the universal
    central-binomial Catalan object `catN` — generalizing the table-only
    `catalan_growth_ratio` (n = 0..6, by `decide`) to all `n`.

    From the ratio recurrence `(n+2)·catN(n+1) = (4n+2)·catN n` and
    `4n+2 ≤ 4(n+2) = 4n+8`, so `(n+2)·catN(n+1) ≤ (n+2)·(4·catN n)`; cancel the
    positive `(n+2)`. -/
theorem catN_growth_bound (n : Nat) : catN (n + 1) ≤ 4 * catN n := by
  have hrec : (n + 2) * catN (n + 1) = (4 * n + 2) * catN n :=
    succ_mul_catN_recurrence_4np2 n
  have hcoef : (4 * n + 2) ≤ (4 * n + 8) :=
    Nat.add_le_add_left (by decide) (4 * n)
  have hmul : (4 * n + 2) * catN n ≤ (4 * n + 8) * catN n :=
    Nat.mul_le_mul_right (catN n) hcoef
  have hform : (4 * n + 8) * catN n = (n + 2) * (4 * catN n) := by
    rw [← mul_assoc (n + 2) 4 (catN n)]
    rw [show (n + 2) * 4 = 4 * n + 8 from by ring_nat]
  have hle : (n + 2) * catN (n + 1) ≤ (n + 2) * (4 * catN n) := by
    rw [hrec, ← hform]; exact hmul
  exact Nat.le_of_mul_le_mul_left hle (Nat.succ_pos (n + 1))

/-- Smoke: the general bound at n = 5 (`C₆ = 132 ≤ 4·42`). -/
theorem catN_growth_smoke : catN 6 ≤ 4 * catN 5 := catN_growth_bound 5

/-! ## Catalan reflection / André's ballot formula -/

/-- **Key absorption**: `(n+1)·choose (2n) (n+1) = n·choose (2n) n`.

    From `choose_succ_mul (2n) n : (n+1)·choose (2n+1) (n+1) = (2n+1)·choose (2n) n`
    and Pascal `choose (2n+1) (n+1) = choose (2n) n + choose (2n) (n+1)`; the common
    `(n+1)·choose (2n) n` is additively cancelled (subtraction-free). -/
theorem choose_central_succ (n : Nat) :
    (n + 1) * choose (2 * n) (n + 1) = n * choose (2 * n) n := by
  have hkey : (n + 1) * choose (2 * n + 1) (n + 1)
      = (2 * n + 1) * choose (2 * n) n := choose_succ_mul (2 * n) n
  rw [choose_succ_succ (2 * n) n, Nat.mul_add] at hkey
  have hsplit : (2 * n + 1) * choose (2 * n) n
      = (n + 1) * choose (2 * n) n + n * choose (2 * n) n := by
    rw [show 2 * n + 1 = (n + 1) + n from by ring_nat,
        E213.Tactic.NatHelper.add_mul (n + 1) n (choose (2 * n) n)]
  rw [hsplit] at hkey
  exact add_left_cancel hkey

/-- **`catN` form of the absorption**: `choose (2n) (n+1) = n · catN n`. -/
theorem choose_central_succ_catN (n : Nat) :
    choose (2 * n) (n + 1) = n * catN n := by
  have h1 : (n + 1) * choose (2 * n) (n + 1) = n * choose (2 * n) n :=
    choose_central_succ n
  have h2 : (n + 1) * catN n = choose (2 * n) n := succ_mul_catN n
  have h3 : (n + 1) * choose (2 * n) (n + 1) = (n + 1) * (n * catN n) := by
    rw [h1, ← h2]; ring_nat
  exact mul_left_cancel_pos (Nat.succ_pos n) h3

/-- ★ **Catalan reflection / ballot formula** (∅-axiom):
    `catN n + choose (2n) (n+1) = choose (2n) n`, i.e. `C_n = C(2n,n) − C(2n,n+1)`
    in subtraction-free form. -/
theorem catalan_reflection (n : Nat) :
    catN n + choose (2 * n) (n + 1) = choose (2 * n) n := by
  rw [choose_central_succ_catN n]
  have h : catN n + n * catN n = (n + 1) * catN n := by ring_nat
  rw [h, succ_mul_catN n]

/-- Smoke: `catN 3 + choose 6 4 = choose 6 3` (`5 + 15 = 20`). -/
theorem catalan_reflection_smoke : catN 3 + choose 6 4 = choose 6 3 := by decide

end E213.Lib.Math.Combinatorics.CatalanBinomial
