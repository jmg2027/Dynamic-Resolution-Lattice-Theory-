import E213.Lib.Math.NumberTheory.BigOmega

/-!
# `mulDescentRec` — the multiplicative descent as `Ω`-count induction

The genesis-seam frontier (`research-notes/frontiers/the_genesis_seam.md`) located the
"generated vs borrowed" terminus at the **multiplicative descent**: `factorize` /
`factorize_prod` complete on `Nat.strongRecOn` over the *magnitude* `n` (the borrowed
kernel well-order), because the peel `n ↦ n / minFac n` is non-structural over `Nat`.

`BigOmega` showed the descent's well-foundedness is really the **prime-count** `Ω`
(the `×`-dual of `Raw.leaves`): `Omega_descent` (`Ω (n/minFac n) + 1 = Ω n`) — each
peel drops the count by exactly one — and `no_infinite_mul_descent`.

This file cashes that out as a **recursion principle**:

  `mulDescentRec` — to prove `P n` for every `n ≥ 1`, give `P 1` and the peel step
  `P (n / minFac n) → P n` (for `n ≥ 2`).  Its proof recurses on the **`Ω`-count**
  (`Nat.rec` over `Ω n`), with each step justified by `Omega_descent` — *not*
  `Nat.strongRecOn` over the magnitude `n`.

So the multiplicative descent "completes on the count's own well-foundedness": the
descent **measure** is the Raw-native leaf-count `Ω` (the count-shadow of the `×`-atom
structure), the magnitude `n` appearing only as the thing being peeled.  `mulDescentRec`
makes this the canonical way to do multiplicative induction in the corpus.

**Honest scope**: this does not escape CIC's `Nat.rec` — induction on the count `Ω n`
*is* `Nat.rec` on a `Nat`.  The claim is narrower and exact: the **well-order driving the
peel is `Ω`** (a leaves-shadow), made explicit, replacing the opaque `strongRecOn`-over-`n`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MulDescentRec

open E213.Lib.Math.NumberTheory.PrimeFactorization
  (minFac minFac_div minFac_prime prodL prodL_cons factorize factorize_prod factorize_all_prime)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.FTAUniqueness (countOcc factorization_unique)
open E213.Lib.Math.NumberTheory.BigOmega
  (Omega Omega_descent Omega_one Omega_def length_eq_of_countOcc_eq)

/-! ## Supporting `Ω`-facts -/

/-- `Ω` is positive on `n ≥ 2`: the count is at least the one factor `minFac n`. -/
theorem Omega_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < Omega n :=
  (Omega_descent hn) ▸ Nat.succ_pos _

/-- The only `n ≥ 1` with `Ω n = 0` is `1`. -/
theorem eq_one_of_Omega_zero {n : Nat} (hn : 1 ≤ n) (hΩ : Omega n = 0) : n = 1 := by
  have hnot2 : ¬ 2 ≤ n := fun h2 => Nat.noConfusion ((Omega_descent h2).trans hΩ)
  have hle1 : n ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_le hnot2)
  exact Nat.le_antisymm hle1 hn

/-- The peel keeps a positive quotient: `minFac n ∣ n` and `n ≥ 2`, so `n / minFac n ≥ 1`. -/
theorem quot_pos {n : Nat} (hn : 2 ≤ n) : 1 ≤ n / minFac n := by
  obtain ⟨hprod, _⟩ := minFac_div hn
  apply Nat.pos_of_ne_zero
  intro hq0
  have hmz : minFac n * 0 = n := hq0 ▸ hprod
  have hn0 : n = 0 := hmz.symm.trans (Nat.mul_zero (minFac n))
  exact absurd (hn0 ▸ hn) (by decide)

/-! ## The recursor -/

/-- ★★★ **Multiplicative-descent recursion principle.**  Prove `P n` for every `n ≥ 1`
    from `P 1` and the peel step `P (n / minFac n) → P n` (`n ≥ 2`).  The proof recurses
    on the prime-count `Ω n` (the `×`-dual leaf-count) via `Omega_descent` — the descent
    **measure is `Ω`**, not the magnitude `n`.  ∅-axiom. -/
theorem mulDescentRec (P : Nat → Prop)
    (base : P 1) (step : ∀ n, 2 ≤ n → P (n / minFac n) → P n) :
    ∀ n, 1 ≤ n → P n := by
  suffices h : ∀ k n, Omega n = k → 1 ≤ n → P n from
    fun n hn => h (Omega n) n rfl hn
  intro k
  induction k with
  | zero =>
    intro n hΩ hn
    exact (eq_one_of_Omega_zero hn hΩ) ▸ base
  | succ k ih =>
    intro n hΩ hn
    have hpos : 0 < Omega n := hΩ.symm ▸ Nat.succ_pos k
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
        have hΩ0 : Omega n = 0 := hn1.symm ▸ Omega_one
        exact absurd (hΩ0 ▸ hpos) (Nat.lt_irrefl 0)
      · exact hge
    have hΩq : Omega (n / minFac n) = k :=
      Nat.succ.inj ((Omega_descent hn2).trans hΩ)
    exact step n hn2 (ih (n / minFac n) hΩq (quot_pos hn2))

/-! ## Demonstration — FTA-existence proves *through* `mulDescentRec` -/

/-- ★★★ **Factorization existence via the count-descent recursor.**  Every `n ≥ 1` is a
    product of primes — proved by `mulDescentRec`, so the recursion completes on the
    `Ω`-count, not `Nat.strongRecOn` over `n`.  (`PrimeFactorization` proves the same on
    `strongRecOn`; this is the *generated* reading: the witness `minFac n :: …` is peeled
    along the count-shadow.)  ∅-axiom. -/
theorem mul_factorization_exists :
    ∀ n, 1 ≤ n → ∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n := by
  refine mulDescentRec
    (fun n => ∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n) ?_ ?_
  · refine ⟨[], ?_, rfl⟩
    intro p hp
    cases hp
  · intro n hn2 hP
    obtain ⟨L', hL'prime, hL'prod⟩ := hP
    refine ⟨minFac n :: L', ?_, ?_⟩
    · intro p hp
      cases hp with
      | head => exact minFac_prime hn2
      | tail _ h => exact hL'prime p h
    · obtain ⟨hprod, _⟩ := minFac_div hn2
      show minFac n * prodL L' = n
      exact (congrArg (minFac n * ·) hL'prod).trans hprod

/-! ## `Ω` is the well-defined prime count -/

/-- ★★★ **`Ω` counts *any* prime factorization.**  Every prime factorization of `n`
    (a list `L` of primes with `prodL L = n`) has length exactly `Ω n` — so `Ω n` is the
    well-defined total prime count, independent of which factorization is chosen.  This
    is the *uniqueness* face: `factorization_unique` (per-prime count invariance) +
    `length_eq_of_countOcc_eq` (equal counts ⟹ equal length), against the canonical
    witness `factorize n`.  ∅-axiom. -/
theorem Omega_eq_length_of_prime_factorization (n : Nat) (hn : 1 ≤ n)
    (L : List Nat) (hLp : ∀ p, p ∈ L → Prime213 p) (hLprod : prodL L = n) :
    L.length = Omega n := by
  have hfp : ∀ p, p ∈ factorize n → Prime213 p := by
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h1) hn
      intro p hp
      exact nomatch (hn1 ▸ hp : p ∈ factorize 1)
    · exact factorize_all_prime n h2
  have hfprod : prodL (factorize n) = n := factorize_prod n hn
  have heq : prodL L = prodL (factorize n) := hLprod.trans hfprod.symm
  have hco : ∀ q, Prime213 q → countOcc q L = countOcc q (factorize n) :=
    fun q hq => factorization_unique hLp hfp heq q hq
  exact (length_eq_of_countOcc_eq L (factorize n) hLp hfp hco).trans (Omega_def n).symm

/-- ★★★ **FTA, in count form.**  For every `n ≥ 1`: a prime factorization *exists*
    (`mul_factorization_exists`, peeled along the `Ω`-count) and *all* of them have the
    same length `Ω n` (`Omega_eq_length_of_prime_factorization`).  Existence is the
    descent (generation); the shared length is the invariant the descent measures. -/
theorem fta_existence_and_count (n : Nat) (hn : 1 ≤ n) :
    (∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n)
    ∧ (∀ L : List Nat, (∀ p, p ∈ L → Prime213 p) → prodL L = n → L.length = Omega n) :=
  ⟨mul_factorization_exists n hn,
   fun L hLp hLprod => Omega_eq_length_of_prime_factorization n hn L hLp hLprod⟩

end E213.Lib.Math.NumberTheory.MulDescentRec
