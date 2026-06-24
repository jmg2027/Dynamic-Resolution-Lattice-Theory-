import E213.Lib.Math.NumberTheory.PrimeFactorization
import E213.Meta.Nat.SubMod213
import E213.Lib.Math.Foundations.IsPartGroundedInduction

/-!
# FTA existence with **no** `Nat.div`/`Nat.mod` — the descent leg's `lt_wfRel`-free clearance

`MulDescentGrounded` grounded the FTA *descent* in `isPart_wf` (removing `Nat.strongRecOn`), leaving a
residual `Nat.lt_wfRel` isolated to `Nat.div`/`Nat.mod` (kernel WF-recursion).  This file removes it:

  * the divisibility *test* in the least-factor search uses `SubMod213.subMod` (structural repeated
    subtraction) instead of `n % k` — so `minFac'` carries no `Nat.mod`;
  * FTA existence recurses on the **divisibility witness** `q` (from `minFac' n ∣ n`, i.e. `n = minFac'
    n * q`) instead of `n / minFac' n` — so it carries no `Nat.div`;
  * the descent is still `measureInduction_grounded` (grounded in `isPart_wf`).

Result (`mul_factorization_exists_nodiv`): factorisation existence with **no `Nat.div`, no `Nat.mod`,
no `Nat.strongRecOn`, no `Nat.lt_wfRel`** — division and remainder rebuilt from the repo's own
`Nat.sub`, the descent grounded in the distinguishing.  The only `Nat` primitives left are `succ`/`+`/
`*`/`-` (structural) and the structural recursors.  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MulDescentGroundedNoDiv

open E213.Lib.Math.NumberTheory.PrimeFactorization (prodL le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.SubMod213 (subMod subMod_zero_iff_dvd)
open E213.Lib.Math.Foundations.IsPartGroundedInduction (measureInduction_grounded)

/-! ## §1 — least factor search on `subMod` (no `Nat.mod`) -/

/-- Smallest `d ≥ k` dividing `n`, fuel-bounded — divisibility by `subMod n n k` (structural
    subtraction), not `n % k`. -/
def leastFactorFrom' : Nat → Nat → Nat → Nat
  | 0,     _, n => n
  | f + 1, k, n =>
    match subMod n n k with
    | 0     => k
    | _ + 1 => leastFactorFrom' f (k + 1) n

/-- Spec of the search (mirrors `PrimeFactorization.leastFactorFrom_spec`, divisibility via
    `subMod_zero_iff_dvd`). -/
theorem leastFactorFrom'_spec :
    ∀ (fuel k n : Nat), 2 ≤ n → 2 ≤ k → n ≤ k + fuel →
      (∀ d, 2 ≤ d → d < k → ¬ d ∣ n) →
      (2 ≤ leastFactorFrom' fuel k n
        ∧ leastFactorFrom' fuel k n ∣ n
        ∧ leastFactorFrom' fuel k n ≤ n
        ∧ ∀ e, 2 ≤ e → e < leastFactorFrom' fuel k n → ¬ e ∣ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k n hn hk hfuel hbelow
    show (2 ≤ n ∧ n ∣ n ∧ n ≤ n ∧ ∀ e, 2 ≤ e → e < n → ¬ e ∣ n)
    have hkn : n ≤ k := by rw [Nat.add_zero] at hfuel; exact hfuel
    refine ⟨hn, ⟨1, (Nat.mul_one n).symm⟩, Nat.le_refl n, ?_⟩
    intro e he2 helt
    exact hbelow e he2 (Nat.lt_of_lt_of_le helt hkn)
  | succ f ih =>
    intro k n hn hk hfuel hbelow
    have hpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
    have hkpos : 0 < k := Nat.lt_of_lt_of_le (by decide) hk
    show (2 ≤ (match subMod n n k with | 0 => k | _ + 1 => leastFactorFrom' f (k + 1) n)
        ∧ (match subMod n n k with | 0 => k | _ + 1 => leastFactorFrom' f (k + 1) n) ∣ n
        ∧ (match subMod n n k with | 0 => k | _ + 1 => leastFactorFrom' f (k + 1) n) ≤ n
        ∧ ∀ e, 2 ≤ e → e < (match subMod n n k with | 0 => k | _ + 1 => leastFactorFrom' f (k + 1) n) → ¬ e ∣ n)
    rcases Nat.eq_zero_or_pos (subMod n n k) with hmod | hmod
    · -- k ∣ n: result = k
      have hdvd : k ∣ n := (subMod_zero_iff_dvd n k hkpos).mp hmod
      have hbr : (match subMod n n k with | 0 => k | _ + 1 => leastFactorFrom' f (k + 1) n) = k := by
        rw [hmod]
      rw [hbr]
      refine ⟨hk, hdvd, le_of_dvd_pos hpos hdvd, ?_⟩
      intro e he2 helt
      exact hbelow e he2 helt
    · -- k ∤ n: recurse at k+1
      have hmodne : subMod n n k ≠ 0 := fun h => Nat.lt_irrefl 0 (h ▸ hmod)
      have hkndvd : ¬ k ∣ n := fun hd => hmodne ((subMod_zero_iff_dvd n k hkpos).mpr hd)
      have hbr : (match subMod n n k with | 0 => k | _ + 1 => leastFactorFrom' f (k + 1) n)
                  = leastFactorFrom' f (k + 1) n := by
        cases hh : subMod n n k with
        | zero => exact absurd hh hmodne
        | succ m => rfl
      rw [hbr]
      have hfuel' : n ≤ (k + 1) + f := by
        have heq : k + (f + 1) = (k + 1) + f := by rw [Nat.add_succ, Nat.succ_add]
        rw [heq] at hfuel; exact hfuel
      have hk1 : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
      have hbelow' : ∀ d, 2 ≤ d → d < k + 1 → ¬ d ∣ n := by
        intro d hd2 hdlt
        rcases Nat.lt_or_ge d k with hdk | hdk
        · exact hbelow d hd2 hdk
        · have hdeq : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdlt) hdk
          rw [hdeq]; exact hkndvd
      exact ih (k + 1) n hn hk1 hfuel' hbelow'

/-! ## §2 — `minFac'` and its prime-divisor spec -/

/-- `minFac' n` = smallest factor `≥ 2`, divisibility tested by `subMod` (no `Nat.mod`). -/
def minFac' (n : Nat) : Nat := leastFactorFrom' n 2 n

theorem minFac'_spec {n : Nat} (hn : 2 ≤ n) :
    2 ≤ minFac' n ∧ minFac' n ∣ n ∧ minFac' n ≤ n
      ∧ ∀ e, 2 ≤ e → e < minFac' n → ¬ e ∣ n := by
  have hfuel : n ≤ 2 + n := Nat.le_add_left n 2
  exact leastFactorFrom'_spec n 2 n hn (Nat.le_refl 2) hfuel
    (fun d hd2 hlt => absurd hlt (Nat.not_lt_of_le hd2))

/-- The minimal factor `≥ 2` is prime (mirrors `PrimeFactorization.minFac_prime`). -/
theorem minFac'_prime {n : Nat} (hn : 2 ≤ n) : Prime213 (minFac' n) := by
  obtain ⟨hge, hdvd, _hle, hmin⟩ := minFac'_spec hn
  refine ⟨hge, ?_⟩
  intro d hdm
  have hmpos : 0 < minFac' n := Nat.lt_of_lt_of_le (by decide) hge
  obtain ⟨c, hc⟩ := hdm
  have hdle : d ≤ minFac' n := le_of_dvd_pos hmpos ⟨c, hc⟩
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · rcases Nat.lt_or_ge d 1 with hd0 | hd1
    · exfalso
      have hd00 : d = 0 := Nat.le_antisymm (Nat.le_of_lt_succ hd0) (Nat.zero_le d)
      rw [hd00, Nat.zero_mul] at hc
      exact Nat.lt_irrefl 0 (hc ▸ hmpos)
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hd2) hd1)
  · obtain ⟨q, hq⟩ := hdvd
    have hdn : d ∣ n := ⟨c * q, by
      calc n = minFac' n * q := hq
        _ = (d * c) * q := by rw [hc]
        _ = d * (c * q) := E213.Tactic.NatHelper.mul_assoc d c q⟩
    rcases Nat.lt_or_ge d (minFac' n) with hdlt | hdge
    · exact absurd hdn (hmin d hd2 hdlt)
    · exact Or.inr (Nat.le_antisymm hdle hdge)

/-! ## §3 — FTA existence on the witness `q` (no `Nat.div`) -/

/-- ★★★ **Factorisation existence with no `Nat.div`/`Nat.mod`/`Nat.strongRecOn`/`Nat.lt_wfRel`.**
    Every `n ≥ 1` is a product of primes.  Descent grounded in `isPart_wf`
    (`measureInduction_grounded`); the prime factor `minFac' n` is found by `subMod` (no `Nat.mod`);
    and the recursion is on the **divisibility witness** `q` with `n = minFac' n * q` (no `Nat.div`).
    So division and remainder are rebuilt from `Nat.sub`, the descent from the distinguishing — the
    descent leg's `lt_wfRel`-free clearance for the multiplicative discipline.  ∅-axiom. -/
theorem mul_factorization_exists_nodiv :
    ∀ n, 1 ≤ n → ∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n := by
  refine measureInduction_grounded (fun n => n)
    (P := fun n => 1 ≤ n → ∃ L : List Nat, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n) ?_
  intro n ih hn
  rcases Nat.lt_or_ge n 2 with hlt | h2
  · have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
    subst hn1
    exact ⟨[], fun p hp => absurd hp (List.not_mem_nil p), rfl⟩
  · obtain ⟨hge, hdvd, hle, _⟩ := minFac'_spec h2
    obtain ⟨q, hq⟩ := hdvd          -- hq : n = minFac' n * q
    have hpos : 0 < n := Nat.lt_of_lt_of_le (by decide) h2
    have hqpos : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exfalso
        rw [h0, Nat.mul_zero] at hq
        exact Nat.lt_irrefl 0 (hq ▸ hpos)
      · exact h0
    have hqlt : q < n := by
      -- n = minFac' n * q ≥ 2 * q > q  (minFac' ≥ 2, q ≥ 1)
      have h2q : 2 * q ≤ minFac' n * q := Nat.mul_le_mul hge (Nat.le_refl q)
      have hnq : 2 * q ≤ n := by rw [hq]; exact h2q
      have hqq : q < 2 * q := by
        have : q + q = 2 * q := (Nat.two_mul q).symm
        exact this ▸ Nat.lt_add_of_pos_right hqpos
      exact Nat.lt_of_lt_of_le hqq hnq
    obtain ⟨L', hL'prime, hL'prod⟩ := ih q hqlt hqpos
    refine ⟨minFac' n :: L', ?_, ?_⟩
    · intro p hp
      cases hp with
      | head => exact minFac'_prime h2
      | tail _ h => exact hL'prime p h
    · show minFac' n * prodL L' = n
      exact (congrArg (minFac' n * ·) hL'prod).trans hq.symm

end E213.Lib.Math.NumberTheory.MulDescentGroundedNoDiv
