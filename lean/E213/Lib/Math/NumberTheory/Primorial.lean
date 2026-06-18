import E213.Lib.Math.NumberTheory.BinomChooseBridge
import E213.Lib.Math.NumberTheory.OddCentralBinom
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Meta.Nat.VpSeparation

/-!
# The primorial bound `∏_{p≤N} p ≤ 4ⁿ` — the Bertrand keystone (∅-axiom, in progress)

Assembles the landed Bertrand keystones (`binom_eq_choose`, `odd_central_binom_le`,
`primesIn_split`, `listProd_append`) into the primorial bound.  Stays in `choose`
(Lib-native) and reaches the Lens `primesIn`/`listProd` machinery through the
`Lens.Number` umbrella (imported transitively via `BinomChooseBridge`).
-/

namespace E213.Lib.Math.NumberTheory.Primorial

open E213.Lens.Number.Nat213.MultSystemValue
  (fact fact_pos dvd_fact prime_not_dvd_fact primesIn listProd listProd_dvd
   primesIn_nodup mem_primesIn_le mem_primesIn_gt mem_primesIn_prime pow_length_le_prod listProd_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul)
open E213.Meta.Nat.Valuation (vp le_vp_iff)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.OddCentralBinom (odd_central_binom_le)

/-- `fact` and `factorial` are the identical recursion (`(n+1)·F n`, base `1`). -/
theorem fact_eq_factorial : ∀ n, fact n = factorial n
  | 0     => rfl
  | n + 1 => by show (n + 1) * fact n = (n + 1) * factorial n; rw [fact_eq_factorial n]

/-- The odd central binomial factorial identity, in `fact`:
    `C(2m+1,m) · (m! · (m+1)!) = (2m+1)!`. -/
theorem odd_binom_factorial (m : Nat) :
    choose (2 * m + 1) m * (fact m * fact (m + 1)) = fact (2 * m + 1) := by
  rw [fact_eq_factorial m, fact_eq_factorial (m + 1), fact_eq_factorial (2 * m + 1),
      show 2 * m + 1 = m + (m + 1) from by ring_nat]
  exact choose_mul_factorials m (m + 1)

/-- `0 < C(2m+1, m)`. -/
theorem odd_binom_pos (m : Nat) : 0 < choose (2 * m + 1) m := by
  have hid := odd_binom_factorial m
  rcases Nat.eq_zero_or_pos (choose (2 * m + 1) m) with h0 | h
  · exfalso; rw [h0, Nat.zero_mul] at hid
    exact absurd hid.symm (Nat.ne_of_gt (fact_pos (2 * m + 1)))
  · exact h

/-- ★ **Every prime in `(m+1, 2m+1]` divides `C(2m+1, m)`.**  The vp argument:
    `vp_p(C) = vp_p((2m+1)!) − vp_p(m!) − vp_p((m+1)!) = vp_p((2m+1)!) ≥ 1`
    (`p > m+1` kills both denominator valuations; `p ≤ 2m+1` gives `p ∣ (2m+1)!`). -/
theorem prime_dvd_odd_binom {p m : Nat} (hp : IsPrime213 p)
    (hlt : m + 1 < p) (hle : p ≤ 2 * m + 1) : p ∣ choose (2 * m + 1) m := by
  have hcpos := odd_binom_pos m
  have hfm : 0 < fact m := fact_pos m
  have hfm1 : 0 < fact (m + 1) := fact_pos (m + 1)
  have hf2 : 0 < fact (2 * m + 1) := fact_pos (2 * m + 1)
  have hvpm : vp p (fact m) = 0 :=
    vp_eq_zero_of_not_dvd hp hfm (prime_not_dvd_fact hp (Nat.lt_trans (Nat.lt_succ_self m) hlt))
  have hvpm1 : vp p (fact (m + 1)) = 0 :=
    vp_eq_zero_of_not_dvd hp hfm1 (prime_not_dvd_fact hp hlt)
  have hvp := congrArg (vp p) (odd_binom_factorial m)
  rw [vp_mul hp hcpos (Nat.mul_pos hfm hfm1), vp_mul hp hfm hfm1, hvpm, hvpm1,
      Nat.add_zero, Nat.add_zero] at hvp
  have hp1 : p ^ 1 ∣ fact (2 * m + 1) := by
    rw [Nat.pow_one]; exact dvd_fact (Nat.lt_of_lt_of_le (by decide) hp.two_le) hle
  have hge1 : 1 ≤ vp p (choose (2 * m + 1) m) := by
    rw [hvp]; exact (le_vp_iff p (fact (2 * m + 1)) 1 hp.two_le hf2).mp hp1
  have hdvd : p ^ 1 ∣ choose (2 * m + 1) m :=
    (le_vp_iff p (choose (2 * m + 1) m) 1 hp.two_le hcpos).mpr hge1
  rwa [Nat.pow_one] at hdvd

/-- The window product `∏_{(m+1, 2m+1]} p` divides `C(2m+1, m)`. -/
theorem window_prod_dvd_odd_binom (m : Nat) :
    listProd (primesIn (m + 1) (2 * m + 1)) ∣ choose (2 * m + 1) m :=
  listProd_dvd
    (fun _ hp => mem_primesIn_prime hp)
    primesIn_nodup
    (odd_binom_pos m)
    (fun _ hp => prime_dvd_odd_binom (mem_primesIn_prime hp) (mem_primesIn_gt hp) (mem_primesIn_le hp))

/-- ★ **`∏_{(m+1, 2m+1]} p ≤ 4^m`** — the upper window's prime product is bounded by the
    odd central binomial it divides. -/
theorem window_prod_le_odd (m : Nat) :
    listProd (primesIn (m + 1) (2 * m + 1)) ≤ 4 ^ m :=
  Nat.le_trans
    (le_of_dvd_pos _ _ (odd_binom_pos m) (window_prod_dvd_odd_binom m))
    (odd_central_binom_le m)


open E213.Lens.Number.Nat213.MultSystemValue (window_prod_le primesIn_split listProd_append)
open E213.Lib.Math.NumberTheory.OddCentralBinom (four_pow_eq)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure)

/-- ★★★★★ **The primorial bound `∏_{p≤N} p ≤ 4ᴺ`** — the Bertrand keystone, ∅-axiom.
    Strong induction with the Erdős parity split: even `N = 2q` reuses `window_prod_le`
    (primes in `(q,2q]`, `≤ 4^q`) + IH(`q`); odd `N = 2q+1` uses `window_prod_le_odd`
    (`≤ 4^q`) + IH(`q+1`); both give `4^q · 4^{(·)} = 4ᴺ`. -/
theorem primorial_le_four_pow : ∀ N, listProd (primesIn 0 N) ≤ 4 ^ N := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    rcases Nat.lt_or_ge N 3 with h3 | h3
    · rcases N with _ | _ | _ | N
      · decide
      · decide
      · decide
      · exact absurd h3 (Nat.not_lt.mpr (Nat.le_add_left 3 N))
    · have hdm : 2 * (N / 2) + N % 2 = N := div_add_mod_pure N 2
      have hmod : N % 2 < 2 := Nat.mod_lt N (by decide)
      have key : ∀ q r, 2 * q + r = N → r < 2 → listProd (primesIn 0 N) ≤ 4 ^ N := by
        intro q r hqr hr
        have hq1 : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with hq0 | hq
          · exfalso; rw [hq0, Nat.mul_zero, Nat.zero_add] at hqr
            rw [← hqr] at h3; exact absurd h3 (Nat.not_le.mpr (Nat.lt_trans hr (by decide)))
          · exact hq
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · -- even: N = 2*q
          have hN : N = 2 * q := by rw [← hqr, hr0, Nat.add_zero]
          have hqle : q ≤ 2 * q := by rw [Nat.two_mul]; exact Nat.le_add_left _ _
          have hqlt : q < N := by
            rw [hN, Nat.two_mul]; exact Nat.lt_add_of_pos_left hq1
          rw [hN, primesIn_split (Nat.zero_le q) hqle, listProd_append]
          have hwin : listProd (primesIn q (2 * q)) ≤ 4 ^ q := by
            have hw := window_prod_le q; rw [← four_pow_eq] at hw; exact hw
          calc listProd (primesIn q (2 * q)) * listProd (primesIn 0 q)
              ≤ 4 ^ q * 4 ^ q := Nat.mul_le_mul hwin (ih q hqlt)
            _ = 4 ^ (2 * q) := by rw [← pow_add, Nat.two_mul]
        · -- odd: N = 2*q+1
          have hr1 : r = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hr) hrpos
          have hN : N = 2 * q + 1 := by rw [← hqr, hr1]
          have hmidle : q + 1 ≤ 2 * q + 1 := by
            rw [Nat.two_mul]; exact Nat.add_le_add_right (Nat.le_add_left _ _) 1
          have hqlt : q + 1 < N := by
            rw [hN, Nat.two_mul]
            exact Nat.add_lt_add_right (Nat.lt_add_of_pos_right hq1) 1
          rw [hN, primesIn_split (Nat.zero_le (q + 1)) hmidle, listProd_append]
          calc listProd (primesIn (q + 1) (2 * q + 1)) * listProd (primesIn 0 (q + 1))
              ≤ 4 ^ q * 4 ^ (q + 1) := Nat.mul_le_mul (window_prod_le_odd q) (ih (q + 1) hqlt)
            _ = 4 ^ (2 * q + 1) := by rw [← pow_add, show q + (q + 1) = 2 * q + 1 from by ring_nat]
      exact key (N / 2) (N % 2) hdm hmod


/-- ★ **Upper-window prime-count bound**: `(m+2)^{π(2m+1)−π(m+1)} ≤ 4^m`.  Each of the
    primes in `(m+1, 2m+1]` exceeds `m+1` (so is `≥ m+2`), and their product is `≤ 4^m`
    (`window_prod_le_odd`); taking the count-th root caps the number of such primes — a
    primorial corollary (the odd-window analogue of `windowCount_pow_le`). -/
theorem upper_window_count_pow_le (m : Nat) :
    (m + 2) ^ (primesIn (m + 1) (2 * m + 1)).length ≤ 4 ^ m :=
  Nat.le_trans
    (pow_length_le_prod (m + 2) (primesIn (m + 1) (2 * m + 1)) (fun _ hp => mem_primesIn_gt hp))
    (window_prod_le_odd m)


/-- ★ **Prime-count bound on `(N/2, N]`**: `(N/2+1)^{π(N)−π(N/2)} ≤ 4ᴺ`.  The primes in
    `(N/2, N]` each exceed `N/2`, and their product is a factor of `∏_{p≤N} p ≤ 4ᴺ` (split
    at `N/2`), so the count is capped — a Chebyshev-type upper bound on `π(N) − π(N/2)`
    straight from the primorial. -/
theorem prime_count_window_le (N : Nat) :
    (N / 2 + 1) ^ (primesIn (N / 2) N).length ≤ 4 ^ N := by
  have hle : N / 2 ≤ N := by
    have h := div_add_mod_pure N 2
    calc N / 2 ≤ 2 * (N / 2) := by rw [Nat.two_mul]; exact Nat.le_add_left _ _
      _ ≤ 2 * (N / 2) + N % 2 := Nat.le_add_right _ _
      _ = N := h
  have hsplit : primesIn 0 N = primesIn (N / 2) N ++ primesIn 0 (N / 2) :=
    primesIn_split (Nat.zero_le _) hle
  have hposB : 0 < listProd (primesIn 0 (N / 2)) :=
    listProd_pos (fun p hp =>
      Nat.lt_of_lt_of_le (by decide) (mem_primesIn_prime hp).two_le)
  have hlow : listProd (primesIn (N / 2) N) ≤ 4 ^ N :=
    calc listProd (primesIn (N / 2) N)
        ≤ listProd (primesIn (N / 2) N) * listProd (primesIn 0 (N / 2)) :=
          Nat.le_mul_of_pos_right _ hposB
      _ = listProd (primesIn (N / 2) N ++ primesIn 0 (N / 2)) := (listProd_append _ _).symm
      _ = listProd (primesIn 0 N) := by rw [← hsplit]
      _ ≤ 4 ^ N := primorial_le_four_pow N
  exact Nat.le_trans
    (pow_length_le_prod (N / 2 + 1) (primesIn (N / 2) N) (fun _ hp => mem_primesIn_gt hp))
    hlow
end E213.Lib.Math.NumberTheory.Primorial
