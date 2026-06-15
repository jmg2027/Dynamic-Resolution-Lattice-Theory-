import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.Pow213

/-!
# Sylvester's sequence — telescoping product + pairwise coprimality (∅-axiom)

Sylvester's sequence `a_0 = 2`, `a_{n+1} = a_n·(a_n − 1) + 1`, giving
`2, 3, 7, 43, 1807, 3263443, …`.

Two genuinely-absent classical facts, built PURE over `Nat`:

* ★★★ **Telescoping product** (subtraction-free form):
    `sylProd n + 1 = syl n`,
  i.e. `∏_{k<n} a_k = a_n − 1`.

* ★★★ **Pairwise coprimality**: for `m < n`,
    `gcd213 (syl m) (syl n) = 1`.
  Cleaner than the Fermat/Goldbach case: the telescoping difference is
  `1` (not `2`), so any common divisor of `a_m, a_n` divides `1` —
  no oddness argument needed.  Sylvester's sequence is the
  fastest-growing sequence of pairwise-coprime integers (Znám's
  problem / Egyptian fractions).

* ★ Each `syl n` carries a prime factor, all distinct (an elementary
  infinitude-of-primes corollary of coprimality).

Structural template: `lean/E213/Lib/Math/NumberTheory/FermatNumbers.lean`.
All `#print axioms` are clean — see `tools/scan_axioms.py`.
-/

namespace E213.Lib.Math.NumberTheory.SylvesterSequence

open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest
  dvd_sub_213)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right mul_assoc)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## Definitions -/

/-- `syl 0 = 2`, `syl (n+1) = syl n · (syl n − 1) + 1`.
    Values `2, 3, 7, 43, 1807, 3263443, …`.  Since `syl n ≥ 1`, the
    `− 1` is honest; the telescoping proof substitutes
    `syl n = sylProd n + 1` so the subtraction reduces by
    `add_sub_cancel_right`. -/
def syl : Nat → Nat
  | 0     => 2
  | n + 1 => syl n * (syl n - 1) + 1

/-- `sylProd n = ∏_{k<n} syl k`, structural recursion. -/
def sylProd : Nat → Nat
  | 0     => 1
  | n + 1 => sylProd n * syl n

/-! ## Concrete smokes (closed numeric `decide`, axiom-clean) -/

theorem syl0 : syl 0 = 2 := by decide
theorem syl1 : syl 1 = 3 := by decide
theorem syl2 : syl 2 = 7 := by decide
theorem syl3 : syl 3 = 43 := by decide
theorem syl4 : syl 4 = 1807 := by decide

theorem sylProd1 : sylProd 1 = 2 := by decide
theorem sylProd2 : sylProd 2 = 6 := by decide
theorem sylProd3 : sylProd 3 = 42 := by decide
theorem sylProd4 : sylProd 4 = 1806 := by decide

theorem prod_smoke2 : sylProd 2 + 1 = syl 2 := by decide
theorem prod_smoke3 : sylProd 3 + 1 = syl 3 := by decide
theorem prod_smoke4 : sylProd 4 + 1 = syl 4 := by decide

theorem gcd_smoke_1_3 : gcd213 (syl 1) (syl 3) = 1 := by decide
theorem gcd_smoke_0_2 : gcd213 (syl 0) (syl 2) = 1 := by decide
theorem gcd_smoke_2_4 : gcd213 (syl 2) (syl 4) = 1 := by decide

/-! ## ★★★ Telescoping product (subtraction-free) -/

/-- ★★★ **Telescoping product** in subtraction-free form:
    `sylProd n + 1 = syl n`, i.e. `∏_{k<n} a_k = a_n − 1`.

    Induction.  With `p = sylProd n`, the hypothesis is `p + 1 = syl n`.
    Then `sylProd (n+1) + 1 = p · syl n + 1`.  Substituting
    `syl n = p + 1` and using `(p + 1) − 1 = p` (so the recurrence's
    `syl n · (syl n − 1) + 1` becomes `(p + 1) · p + 1`), both sides
    reduce to `p · (p + 1) + 1` by commutativity — no nonlinear
    `ring` step needed. -/
theorem sylProd_add_one : ∀ n, sylProd n + 1 = syl n
  | 0       => by decide
  | (n + 1) => by
    have ih : sylProd n + 1 = syl n := sylProd_add_one n
    -- target: sylProd (n+1) + 1 = syl (n+1)
    show sylProd n * syl n + 1 = syl n * (syl n - 1) + 1
    -- substitute syl n = sylProd n + 1 on both sides
    rw [← ih]
    -- goal: sylProd n * (sylProd n + 1) + 1
    --        = (sylProd n + 1) * ((sylProd n + 1) - 1) + 1
    have hsub : (sylProd n + 1) - 1 = sylProd n := add_sub_cancel_right (sylProd n) 1
    rw [hsub]
    -- goal: sylProd n * (sylProd n + 1) + 1 = (sylProd n + 1) * sylProd n + 1
    rw [Nat.mul_comm (sylProd n + 1) (sylProd n)]

/-! ## Divisibility of the product by earlier Sylvester numbers -/

/-- `syl m ∣ sylProd n` whenever `m < n`. -/
theorem syl_dvd_prod : ∀ {m n : Nat}, m < n → syl m ∣ sylProd n
  | m, 0,       h => absurd h (Nat.not_lt_zero m)
  | m, (n + 1), h => by
    show syl m ∣ sylProd n * syl n
    rcases Nat.lt_or_ge m n with hlt | hge
    · -- m < n: recurse, syl m ∣ sylProd n, then ∣ product
      rcases syl_dvd_prod hlt with ⟨c, hc⟩
      exact ⟨c * syl n, by rw [hc]; rw [mul_assoc]⟩
    · -- m ≥ n and m < n+1 ⟹ m = n
      have hmn : m = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
      exact ⟨sylProd n, by rw [hmn]; rw [Nat.mul_comm]⟩

/-! ## ★★★ Pairwise coprimality -/

/-- Any common divisor `g` of `syl m` and `syl n` (with `m < n`)
    divides `1`.  Because `g ∣ syl n` and `g ∣ sylProd n`
    (via `syl m ∣ sylProd n`), and `sylProd n + 1 = syl n`, so `g`
    divides the difference `syl n − sylProd n = 1`. -/
theorem common_divisor_dvd_one {m n : Nat} (h : m < n)
    {g : Nat} (hgm : g ∣ syl m) (hgn : g ∣ syl n) : g ∣ 1 := by
  -- g ∣ sylProd n (through syl m) — PURE dvd transitivity inline
  have hgp : g ∣ sylProd n := by
    rcases hgm with ⟨a, ha⟩
    rcases syl_dvd_prod h with ⟨b, hb⟩
    exact ⟨a * b, by rw [hb, ha, mul_assoc]⟩
  -- sylProd n + 1 = syl n ⟹ 1 = syl n - sylProd n
  have hsum : sylProd n + 1 = syl n := sylProd_add_one n
  have hle : sylProd n ≤ syl n := by
    rw [← hsum]; exact Nat.le_add_right _ _
  -- g ∣ (syl n - sylProd n) = 1
  have hd : g ∣ (syl n - sylProd n) := dvd_sub_213 _ _ g hle hgp hgn
  have h1 : syl n - sylProd n = 1 := by
    rw [← hsum]; rw [Nat.add_comm]
    exact add_sub_cancel_right 1 _
  rw [h1] at hd; exact hd

/-- ★★★ **Pairwise coprimality**: for `m < n`,
    `gcd213 (syl m) (syl n) = 1`.

    Let `g = gcd213 (a_m) (a_n)`.  Then `g ∣ 1` (above), hence `g ≤ 1`
    and `g ≠ 0`, forcing `g = 1`. -/
theorem syl_coprime {m n : Nat} (h : m < n) :
    gcd213 (syl m) (syl n) = 1 := by
  have hgm : gcd213 (syl m) (syl n) ∣ syl m := gcd213_dvd_left _ _
  have hgn : gcd213 (syl m) (syl n) ∣ syl n := gcd213_dvd_right _ _
  -- g ∣ 1
  have hg1 : gcd213 (syl m) (syl n) ∣ 1 := common_divisor_dvd_one h hgm hgn
  -- g ≤ 1
  have hle : gcd213 (syl m) (syl n) ≤ 1 := le_of_dvd_pos _ 1 (by decide) hg1
  -- g ≠ 0 (else 0 ∣ 1 ⟹ 1 = 0)
  have hne0 : gcd213 (syl m) (syl n) ≠ 0 := by
    intro he
    rcases hg1 with ⟨c, hc⟩
    rw [he, Nat.zero_mul] at hc
    exact absurd hc.symm (by decide)
  -- g ≤ 1 and g ≠ 0 ⟹ g = 1
  rcases Nat.lt_or_ge (gcd213 (syl m) (syl n)) 1 with h1 | h1
  · exact absurd (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h1)) hne0
  · exact Nat.le_antisymm hle h1

/-! ## ★ Distinct prime factors (infinitude-of-primes corollary) -/

/-- A prime-style witness: if `p ∣ syl m` with `p > 1` and `m < n`,
    then `p ∤ syl n`.  Direct from coprimality — each `syl n` carries
    prime factors disjoint from all earlier terms, so the sequence
    exhibits infinitely many primes (Euclid–Mullin flavor). -/
theorem prime_factor_not_shared {m n p : Nat} (h : m < n) (hp : 1 < p)
    (hpm : p ∣ syl m) (hpn : p ∣ syl n) : False := by
  -- p ∣ gcd213 (syl m) (syl n) = 1, but p > 1
  have hpg : p ∣ gcd213 (syl m) (syl n) :=
    gcd213_greatest (syl m) (syl n) p hpm hpn
  rw [syl_coprime h] at hpg
  have hple : p ≤ 1 := le_of_dvd_pos p 1 (by decide) hpg
  exact absurd hple (Nat.not_le_of_gt hp)

end E213.Lib.Math.NumberTheory.SylvesterSequence
