import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial

/-!
# The central binomial coefficient is even — `2 ∣ C(2n, n)` for `n ≥ 1` (∅-axiom)

An elementary divisibility fact (the Kummer-lite / Lucas-mod-2 corollary): the
central binomial coefficient `C(2m, m)` is even for every `m ≥ 1`.  Pure Pascal +
symmetry, no factorials, no `vp`:

  * Pascal:    `C(2n+2, n+1) = C(2n+1, n) + C(2n+1, n+1)`
  * Symmetry:  `C(2n+1, n) = C(2n+1, n+1)`   (from `n + (n+1) = 2n+1`)
  * Hence      `C(2n+2, n+1) = 2 · C(2n+1, n+1)`, so `2 ∣ C(2m, m)`.

Genuinely absent: the corpus `prime_dvd_central_binom` needs a prime `p` with
`n < p ≤ 2n` (for `p = 2` that window only catches `n = 1`); this is the all-`n`
statement.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.CentralBinomEven

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_succ_succ choose_symm_sum)

/-- ★ **Central binomial split**: `C(2n+2, n+1) = 2 · C(2n+1, n+1)`.
    Pascal expands the central coefficient into two halves; binomial symmetry
    (`C(2n+1, n) = C(2n+1, n+1)`) identifies them, collapsing to twice one half. -/
theorem central_succ_eq_two_mul (n : Nat) :
    choose (2 * n + 2) (n + 1) = 2 * choose (2 * n + 1) (n + 1) := by
  have hpascal :
      choose ((2 * n + 1) + 1) (n + 1)
        = choose (2 * n + 1) n + choose (2 * n + 1) (n + 1) :=
    choose_succ_succ (2 * n + 1) n
  have hsymm : choose (2 * n + 1) n = choose (2 * n + 1) (n + 1) :=
    choose_symm_sum (2 * n + 1) n (n + 1) (by ring_nat)
  show choose ((2 * n + 1) + 1) (n + 1) = 2 * choose (2 * n + 1) (n + 1)
  rw [hpascal, hsymm]
  exact (Nat.two_mul _).symm

/-- ★★ **Central binomial coefficient is even**: `2 ∣ C(2m, m)` for `m ≥ 1`.
    Immediate from `central_succ_eq_two_mul` at `m = n+1`. -/
theorem two_dvd_central_binom : ∀ {m : Nat}, 0 < m → 2 ∣ choose (2 * m) m
  | n + 1, _ => by
    have hsplit := central_succ_eq_two_mul n
    have he : 2 * (n + 1) = 2 * n + 2 := by ring_nat
    rw [he, hsplit]
    exact ⟨choose (2 * n + 1) (n + 1), rfl⟩

/-! ## Smoke — concrete central coefficients `2, 6, 20` -/

theorem two_dvd_central_1 : 2 ∣ choose 2 1 := two_dvd_central_binom (m := 1) (by decide)
theorem two_dvd_central_2 : 2 ∣ choose 4 2 := two_dvd_central_binom (m := 2) (by decide)
theorem two_dvd_central_3 : 2 ∣ choose 6 3 := two_dvd_central_binom (m := 3) (by decide)

theorem central_values :
    choose 2 1 = 2 ∧ choose 4 2 = 6 ∧ choose 6 3 = 20 := by decide

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.CentralBinomEven
