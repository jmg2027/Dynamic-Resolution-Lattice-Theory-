import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.Iterate213
import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.Pow213

/-!
# Fermat numbers `F_n = 2^(2^n) + 1` — telescoping product + Goldbach coprimality (∅-axiom)

Two genuinely-absent classical facts, built PURE over `Nat`:

* ★★★ **Telescoping product** (subtraction-free):
    `fermatProd n + 2 = fermat n`,
  i.e. `∏_{k<n} F_k = F_n − 2`.

* ★★★ **Goldbach pairwise coprimality**: for `m < n`,
    `gcd213 (fermat m) (fermat n) = 1`.
  Consequence: each `F_n` carries a prime factor, all distinct
  (an elementary proof of the infinitude of primes).

All `#print axioms` are clean — see `tools/scan_axioms.py`.
-/

namespace E213.Lib.Math.NumberTheory.FermatNumbers

open E213.Meta.Nat.Iterate213 (pow_pow_eq_pow_mul pow_add_from_iter)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest
  dvd_sub_213 dvd_add_213 dvd_antisymm_213)
open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## Definitions -/

/-- `fermat n = 2^(2^n) + 1`.  `F_0=3, F_1=5, F_2=17, F_3=257, F_4=65537`. -/
def fermat (n : Nat) : Nat := 2 ^ (2 ^ n) + 1

/-- `fermatProd n = ∏_{k<n} fermat k`, structural recursion. -/
def fermatProd : Nat → Nat
  | 0     => 1
  | n + 1 => fermatProd n * fermat n

/-! ## Concrete smokes (closed numeric `decide`, axiom-clean) -/

theorem fermat0 : fermat 0 = 3 := by decide
theorem fermat1 : fermat 1 = 5 := by decide
theorem fermat2 : fermat 2 = 17 := by decide
theorem fermat3 : fermat 3 = 257 := by decide
theorem fermat4 : fermat 4 = 65537 := by decide

theorem fermatProd1 : fermatProd 1 = 3 := by decide
theorem fermatProd2 : fermatProd 2 = 15 := by decide
theorem fermatProd3 : fermatProd 3 = 255 := by decide

theorem prod_smoke2 : fermatProd 2 + 2 = fermat 2 := by decide
theorem prod_smoke3 : fermatProd 3 + 2 = fermat 3 := by decide

theorem gcd_smoke_1_3 : gcd213 (fermat 1) (fermat 3) = 1 := by decide
theorem gcd_smoke_0_2 : gcd213 (fermat 0) (fermat 2) = 1 := by decide
theorem gcd_smoke_2_4 : gcd213 (fermat 2) (fermat 4) = 1 := by decide

/-! ## Power lemma:  `2^(2^(n+1)) = (2^(2^n))^2` -/

/-- `2^(2^(n+1)) = (2^(2^n))·(2^(2^n))`.  Subtraction-free; via
    `2^(n+1)=2^n·2` and `2^(a·2) = (2^a)·(2^a)`. -/
theorem two_pow_two_pow_succ (n : Nat) :
    2 ^ (2 ^ (n + 1)) = 2 ^ (2 ^ n) * 2 ^ (2 ^ n) := by
  have hexp : (2 : Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [pow_add_from_iter]
    show 2 ^ n * 2 = 2 ^ n + 2 ^ n
    ring_nat
  rw [hexp, pow_add_from_iter]

/-- Pure algebra of the induction step: if `p + 1 = A` then
    `p · (A + 1) + 2 = A · A + 1`.  After substituting `A = p + 1`,
    both sides equal `p² + 2p + 2` (a `ring_nat` identity). -/
theorem step_algebra (p A : Nat) (hp : p + 1 = A) :
    p * (A + 1) + 2 = A * A + 1 := by
  rw [← hp]; ring_nat

/-! ## ★★★ Telescoping product (subtraction-free) -/

/-- ★★★ **Telescoping product** in subtraction-free form:
    `fermatProd n + 2 = fermat n`, i.e. `∏_{k<n} F_k = F_n − 2`.

    Induction.  Write `A = 2^(2^n)`, so `fermat n = A + 1` and the
    hypothesis `fermatProd n + 2 = A + 1` gives `fermatProd n + 1 = A`.
    Then `fermatProd (n+1) = fermatProd n · (A+1)` and
    `fermatProd n · (A+1) + 2 = (fermatProd n + 1) · A + 1 = A·A + 1`,
    so `fermatProd (n+1) + 2 = A·A + 1 = fermat (n+1)`. -/
theorem fermatProd_add_two : ∀ n, fermatProd n + 2 = fermat n
  | 0       => by decide
  | (n + 1) => by
    have ih : fermatProd n + 2 = fermat n := fermatProd_add_two n
    -- p + 1 = 2^(2^n)   (from ih : p + 2 = 2^(2^n) + 1)
    have hp1 : fermatProd n + 1 = 2 ^ (2 ^ n) := by
      have hh : fermatProd n + 1 + 1 = 2 ^ (2 ^ n) + 1 := ih
      exact Nat.succ.inj hh
    -- target: fermatProd (n+1) + 2 = fermat (n+1)
    show fermatProd n * fermat n + 2 = 2 ^ (2 ^ (n + 1)) + 1
    show fermatProd n * (2 ^ (2 ^ n) + 1) + 2 = 2 ^ (2 ^ (n + 1)) + 1
    rw [two_pow_two_pow_succ]
    exact step_algebra (fermatProd n) (2 ^ (2 ^ n)) hp1

/-! ## Divisibility of the product by earlier Fermat numbers -/

/-- `fermat m ∣ fermatProd n` whenever `m < n`. -/
theorem fermat_dvd_prod : ∀ {m n : Nat}, m < n → fermat m ∣ fermatProd n
  | m, 0,       h => absurd h (Nat.not_lt_zero m)
  | m, (n + 1), h => by
    show fermat m ∣ fermatProd n * fermat n
    rcases Nat.lt_or_ge m n with hlt | hge
    · -- m < n: recurse, F_m ∣ fermatProd n, then ∣ product
      rcases fermat_dvd_prod hlt with ⟨c, hc⟩
      exact ⟨c * fermat n, by
        rw [hc]; rw [E213.Tactic.NatHelper.mul_assoc]⟩
    · -- m ≥ n and m < n+1 ⟹ m = n
      have hmn : m = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
      exact ⟨fermatProd n, by rw [hmn]; rw [Nat.mul_comm]⟩

/-! ## Oddness of Fermat numbers -/

/-- `2 ∣ 2^(2^n)` (the power has positive exponent). -/
theorem two_dvd_two_pow (n : Nat) : 2 ∣ 2 ^ (2 ^ n) := by
  -- 2^n = (2^n - 1) + 1, so 2^(2^n) = 2^(2^n-1) * 2
  have hpos : 0 < 2 ^ n := Nat.pos_pow_of_pos n (by decide)
  refine ⟨2 ^ (2 ^ n - 1), ?_⟩
  -- 2^(2^n) = 2 * 2^(2^n - 1)
  have he : 2 ^ n = (2 ^ n - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  calc 2 ^ (2 ^ n)
      = 2 ^ (1 + (2 ^ n - 1)) := by rw [Nat.add_comm]; rw [← he]
    _ = 2 ^ 1 * 2 ^ (2 ^ n - 1) := by rw [pow_add_from_iter]
    _ = 2 * 2 ^ (2 ^ n - 1) := rfl

/-- ★ **Fermat numbers are odd**: `¬ 2 ∣ fermat n`. -/
theorem fermat_odd (n : Nat) : ¬ (2 ∣ fermat n) := by
  intro h
  -- h : 2 ∣ 2^(2^n) + 1 ; 2 ∣ 2^(2^n) ⟹ 2 ∣ 1
  have hpow : 2 ∣ 2 ^ (2 ^ n) := two_dvd_two_pow n
  have : (2 : Nat) ∣ 1 := by
    have hle : 2 ^ (2 ^ n) ≤ fermat n := by
      show 2 ^ (2 ^ n) ≤ 2 ^ (2 ^ n) + 1
      exact Nat.le_succ _
    have := dvd_sub_213 (2 ^ (2 ^ n)) (fermat n) 2 hle hpow h
    -- fermat n - 2^(2^n) = 1
    have he : fermat n - 2 ^ (2 ^ n) = 1 := by
      show 2 ^ (2 ^ n) + 1 - 2 ^ (2 ^ n) = 1
      rw [Nat.add_comm]; exact E213.Tactic.NatHelper.add_sub_cancel_right 1 _
    rw [he] at this; exact this
  -- ¬ (2 ∣ 1), PURE: a divisor c of 1 with 2*c=1 is impossible
  rcases this with ⟨c, hc⟩
  rcases Nat.eq_zero_or_pos c with hc0 | hc1
  · rw [hc0, Nat.mul_zero] at hc; exact absurd hc.symm (by decide)
  · have : 2 ≤ 2 * c := by
      calc (2 : Nat) = 2 * 1 := (Nat.mul_one 2).symm
        _ ≤ 2 * c := Nat.mul_le_mul_left 2 hc1
    rw [← hc] at this; exact absurd this (by decide)

/-! ## ★★★ Goldbach pairwise coprimality -/

/-- Any common divisor `g` of `fermat m` and `fermat n` (with `m < n`)
    divides `2`.  Because `g ∣ fermat n` and `g ∣ fermatProd n`
    (via `fermat m ∣ fermatProd n`), and `fermatProd n + 2 = fermat n`. -/
theorem common_divisor_dvd_two {m n : Nat} (h : m < n)
    {g : Nat} (hgm : g ∣ fermat m) (hgn : g ∣ fermat n) : g ∣ 2 := by
  -- g ∣ fermatProd n (through fermat m) — PURE dvd transitivity inline
  have hgp : g ∣ fermatProd n := by
    rcases hgm with ⟨a, ha⟩
    rcases fermat_dvd_prod h with ⟨b, hb⟩
    exact ⟨a * b, by rw [hb, ha, E213.Tactic.NatHelper.mul_assoc]⟩
  -- fermatProd n + 2 = fermat n ⟹ 2 = fermat n - fermatProd n
  have hsum : fermatProd n + 2 = fermat n := fermatProd_add_two n
  have hle : fermatProd n ≤ fermat n := by
    rw [← hsum]; exact Nat.le_add_right _ _
  -- g ∣ (fermat n - fermatProd n) = 2
  have hd : g ∣ (fermat n - fermatProd n) := dvd_sub_213 _ _ g hle hgp hgn
  have h2 : fermat n - fermatProd n = 2 := by
    rw [← hsum]; rw [Nat.add_comm]
    exact E213.Tactic.NatHelper.add_sub_cancel_right 2 _
  rw [h2] at hd; exact hd

/-- ★★★★★ **Goldbach pairwise coprimality**: for `m < n`,
    `gcd213 (fermat m) (fermat n) = 1`.

    Let `g = gcd213 (F_m) (F_n)`.  Then `g ∣ 2` (above) and `g ∣ F_n`,
    which is odd, so `g ≠ 2`; `g ∣ 2` with `g ≠ 2` forces `g = 1`. -/
theorem fermat_coprime {m n : Nat} (h : m < n) :
    gcd213 (fermat m) (fermat n) = 1 := by
  have hgm : gcd213 (fermat m) (fermat n) ∣ fermat m := gcd213_dvd_left _ _
  have hgn : gcd213 (fermat m) (fermat n) ∣ fermat n := gcd213_dvd_right _ _
  -- g ∣ 2
  have hg2 : gcd213 (fermat m) (fermat n) ∣ 2 :=
    common_divisor_dvd_two h hgm hgn
  -- g ≤ 2
  have hle : gcd213 (fermat m) (fermat n) ≤ 2 :=
    le_of_dvd_pos _ 2 (by decide) hg2
  -- g ≠ 2 (else 2 ∣ fermat n, but fermat n is odd)
  have hne : gcd213 (fermat m) (fermat n) ≠ 2 := by
    intro he
    exact fermat_odd n (he ▸ hgn)
  -- g ≠ 0 (else 0 ∣ 2 ⟹ 2 = 0)
  have hne0 : gcd213 (fermat m) (fermat n) ≠ 0 := by
    intro he
    rcases hg2 with ⟨c, hc⟩
    rw [he, Nat.zero_mul] at hc
    exact absurd hc.symm (by decide)
  -- g ≤ 2, g ≠ 0, g ≠ 2  ⟹  g = 1
  rcases Nat.lt_or_ge (gcd213 (fermat m) (fermat n)) 2 with hlt | hge2
  · -- g < 2 and g ≠ 0 ⟹ g = 1
    rcases Nat.lt_or_ge (gcd213 (fermat m) (fermat n)) 1 with h1 | h1
    · exact absurd (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h1)) hne0
    · exact Nat.le_antisymm (Nat.le_of_lt_succ hlt) h1
  · -- g ≥ 2 and g ≤ 2 ⟹ g = 2, contradiction
    exact absurd (Nat.le_antisymm hle hge2) hne

end E213.Lib.Math.NumberTheory.FermatNumbers
