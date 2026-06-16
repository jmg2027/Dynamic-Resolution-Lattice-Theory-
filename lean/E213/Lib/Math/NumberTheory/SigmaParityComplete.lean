import E213.Lib.Math.NumberTheory.SquareCharacterization
import E213.Lib.Math.NumberTheory.SigmaParity
import E213.Lib.Math.NumberTheory.OddPartDecomposition
import E213.Lib.Math.NumberTheory.MobiusDivisorSum
import E213.Lib.Math.NumberTheory.DivisorMultiplicative
import E213.Meta.Nat.FloorLog
import E213.Meta.Nat.Iterate213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213

/-!
# Capstone: σ(n) odd ⟺ n square or twice-square (∅-axiom)

Completes the general σ-parity theorem.

★★★ `sigma_odd_square_odd (hm1 : 0 < m) (hodd : m % 2 = 1) :
        sigma m % 2 = 1 ↔ IsSquare m`  — strong induction on m.
★★★ `sigma_odd_iff (hn : 0 < n) :
        sigma n % 2 = 1 ↔ ((∃ r, r*r = n) ∨ (∃ r, 2*(r*r) = n))`.

Built from the corpus: `exists_prime_pow_cofactor`, `sigma_mul`,
`sigma_odd_prime_pow_parity`, `coprime_isSquare_mul`, `sigma_odd_iff_oddPart`,
`sq_or_twice_iff`.

New ∅-axiom sub-lemmas: `isSquare_prime_pow_iff` (general prime, generalizes the
`p=2` case `isSquare_two_pow_iff`), `mul_odd_iff`, `odd_of_dvd_odd`.
`dvd_trans_213` is used instead of core `Nat.dvd_trans` (the latter is propext-dirty).
-/

namespace E213.Lib.Math.NumberTheory.SigmaParityComplete

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative (sigma_mul)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.SquareCharacterization
  (IsSquare coprime_isSquare_mul sq_or_twice_iff)
open E213.Lib.Math.NumberTheory.OddPartDecomposition
  (oddPart oddPart_odd oddPart_pos sigma_odd_iff_oddPart)
open E213.Lib.Math.NumberTheory.SigmaParity (sigma_odd_prime_pow_parity)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (exists_prime_pow_cofactor divisor_of_prime_pow_eq)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.FloorLog (pow_lt_pow_of_lt)
open E213.Meta.Nat.Iterate213 (pow_add_from_iter)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (mod_two_zero_or_one div_add_mod add_mod_gen)
open E213.Meta.Nat.NatDiv213 (mul_mod_self_pure)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (dvd_trans_213)

/-! ## §1 — `IsSquare (p^k) ↔ k even` for a general prime `p` -/

/-- `IsSquare (p^k) ↔ k % 2 = 0` — generalizes `isSquare_two_pow_iff` (the `p=2`
    case) to any prime `p`.  A divisor `r` of `p^k` is `p^(vp p r)`; `p^k = r*r`
    forces `k = 2·vp p r` by strict pow-monotonicity (`p ≥ 2`). -/
theorem isSquare_prime_pow_iff {p : Nat} (hp : Prime213 p) (k : Nat) :
    IsSquare (p ^ k) ↔ k % 2 = 0 := by
  have hp2 : 2 ≤ p := hp.1
  constructor
  · rintro ⟨r, hr⟩
    have hrpos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | hpp
      · rw [h0, Nat.zero_mul] at hr
        exact absurd hr.symm
          (Nat.ne_of_gt (Nat.pos_pow_of_pos k (Nat.lt_of_lt_of_le (by decide) hp2)))
      · exact hpp
    have hrdvd : r ∣ p ^ k := ⟨r, hr.symm⟩
    have hrpow : r = p ^ (E213.Meta.Nat.Valuation.vp p r) :=
      divisor_of_prime_pow_eq hp hrpos hrdvd
    have hpow : (p : Nat) ^ k
        = p ^ (E213.Meta.Nat.Valuation.vp p r + E213.Meta.Nat.Valuation.vp p r) := by
      rw [pow_add_from_iter, ← hrpow]
      exact hr.symm
    have hak : k = E213.Meta.Nat.Valuation.vp p r + E213.Meta.Nat.Valuation.vp p r := by
      rcases Nat.lt_trichotomy k (E213.Meta.Nat.Valuation.vp p r
          + E213.Meta.Nat.Valuation.vp p r) with hlt | heq | hgt
      · exact absurd (hpow ▸ pow_lt_pow_of_lt hp2 hlt) (Nat.lt_irrefl _)
      · exact heq
      · exact absurd (hpow.symm ▸ pow_lt_pow_of_lt hp2 hgt) (Nat.lt_irrefl _)
    rw [hak]
    rw [show E213.Meta.Nat.Valuation.vp p r + E213.Meta.Nat.Valuation.vp p r
        = 2 * E213.Meta.Nat.Valuation.vp p r from by ring_nat]
    exact mul_mod_self_pure 2 (E213.Meta.Nat.Valuation.vp p r)
  · intro hk
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := by
      refine ⟨k / 2, ?_⟩
      have hdm : 2 * (k / 2) + k % 2 = k := div_add_mod k 2
      rw [hk, Nat.add_zero] at hdm
      exact hdm.symm
    refine ⟨p ^ m, ?_⟩
    rw [← pow_add_from_iter, hm]
    rw [show m + m = 2 * m from by ring_nat]

/-! ## §2 — parity of a product of Nats -/

/-- `(a*b) % 2 = 1 ↔ (a%2=1 ∧ b%2=1)` — a product of Nats is odd iff both factors
    are odd. -/
theorem mul_odd_iff (a b : Nat) : (a * b) % 2 = 1 ↔ (a % 2 = 1 ∧ b % 2 = 1) := by
  rw [mul_mod_pure a b 2]
  constructor
  · intro h
    rcases mod_two_zero_or_one a with ha | ha
    · rw [ha, Nat.zero_mul] at h; exact absurd h (by decide)
    · rcases mod_two_zero_or_one b with hb | hb
      · rw [hb, Nat.mul_zero] at h; exact absurd h (by decide)
      · exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]

/-! ## §3 — odd-divisor helpers -/

/-- A divisor of an odd number is odd: `d ∣ m`, `m % 2 = 1` ⟹ `d % 2 = 1`. -/
theorem odd_of_dvd_odd {d m : Nat} (hd : d ∣ m) (hm : m % 2 = 1) : d % 2 = 1 := by
  rcases mod_two_zero_or_one d with h0 | h1
  · exfalso
    obtain ⟨c, hc⟩ := hd
    -- d even ⟹ 2 ∣ d ∣ m ⟹ m even, contradiction
    obtain ⟨e, he⟩ : ∃ e, d = 2 * e := by
      refine ⟨d / 2, ?_⟩
      have hdm : 2 * (d / 2) + d % 2 = d := div_add_mod d 2
      rw [h0, Nat.add_zero] at hdm
      exact hdm.symm
    have hmeven : m % 2 = 0 := by
      rw [hc, he, E213.Tactic.NatHelper.mul_assoc]
      exact mul_mod_self_pure 2 (e * c)
    rw [hm] at hmeven; exact absurd hmeven (by decide)
  · exact h1

/-! ## §4 — ★★★ the odd-square σ-parity, by strong induction -/

/-- One inductive step (extracted for axiom-localisation). -/
theorem sigma_odd_square_step (m : Nat)
    (ih : ∀ j, j < m → 0 < j → j % 2 = 1 → (sigma j % 2 = 1 ↔ IsSquare j))
    (hm1 : 0 < m) (hodd : m % 2 = 1) : (sigma m % 2 = 1 ↔ IsSquare m) := by
    rcases Nat.lt_or_ge 1 m with hgt | hle
    · -- m > 1
      obtain ⟨p, k, m', hp, hk1, hm'pos, hm'lt, hcop, hmeq⟩ :=
        exists_prime_pow_cofactor hgt
      have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
      have hpk_pos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
      -- p ∣ p^k ∣ m  (k ≥ 1)
      have hp_dvd_pk : p ∣ p ^ k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk1).symm⟩
        exact ⟨p ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      have hpk_dvd_m : p ^ k ∣ m := ⟨m', hmeq⟩
      have hp_dvd_m : p ∣ m := dvd_trans_213 hp_dvd_pk hpk_dvd_m
      have hp_odd : p % 2 = 1 := odd_of_dvd_odd hp_dvd_m hodd
      -- m' ∣ m
      have hm'_dvd_m : m' ∣ m := ⟨p ^ k, by rw [Nat.mul_comm]; exact hmeq⟩
      have hm'_odd : m' % 2 = 1 := odd_of_dvd_odd hm'_dvd_m hodd
      -- σ(p^k·m') = σ(p^k) * σ(m')
      have hsig : sigma (p ^ k * m') = sigma (p ^ k) * sigma m' :=
        sigma_mul hcop hpk_pos hm'pos
      -- σ(p^k) parity = (k+1)%2 ; odd ⟺ k even
      have hpk_par : sigma (p ^ k) % 2 = (k + 1) % 2 :=
        sigma_odd_prime_pow_parity hp hp_odd k
      have hpk_odd_iff : sigma (p ^ k) % 2 = 1 ↔ k % 2 = 0 := by
        rw [hpk_par]
        constructor
        · intro h
          rcases mod_two_zero_or_one k with hk0 | hk1'
          · exact hk0
          · exfalso
            rw [add_mod_gen k 1 2, hk1'] at h; exact absurd h (by decide)
        · intro h
          rw [add_mod_gen k 1 2, h]
      -- σ(m') parity ⟺ IsSquare m'  by IH
      have hm'_iff : sigma m' % 2 = 1 ↔ IsSquare m' := ih m' hm'lt hm'pos hm'_odd
      -- σ(p^k·m') odd ⟺ (k even ∧ IsSquare m')  — built with Iff combinators (propext-free)
      have hsig_iff : sigma (p ^ k * m') % 2 = 1 ↔ (k % 2 = 0 ∧ IsSquare m') := by
        have step1 :
            sigma (p ^ k * m') % 2 = 1 ↔ (sigma (p ^ k) % 2 = 1 ∧ sigma m' % 2 = 1) := by
          rw [hsig]; exact mul_odd_iff _ _
        refine step1.trans (Iff.intro ?_ ?_)
        · rintro ⟨ha, hb⟩; exact ⟨hpk_odd_iff.mp ha, hm'_iff.mp hb⟩
        · rintro ⟨ha, hb⟩; exact ⟨hpk_odd_iff.mpr ha, hm'_iff.mpr hb⟩
      -- IsSquare (p^k·m') ⟺ (k even ∧ IsSquare m')
      have hsq_iff : IsSquare (p ^ k * m') ↔ (k % 2 = 0 ∧ IsSquare m') := by
        refine (coprime_isSquare_mul hcop).trans (Iff.intro ?_ ?_)
        · rintro ⟨ha, hb⟩; exact ⟨(isSquare_prime_pow_iff hp k).mp ha, hb⟩
        · rintro ⟨ha, hb⟩; exact ⟨(isSquare_prime_pow_iff hp k).mpr ha, hb⟩
      -- transport the goal `… m …` to `… p^k·m' …` via the Nat equation hmeq
      have hgoal : sigma (p ^ k * m') % 2 = 1 ↔ IsSquare (p ^ k * m') :=
        hsig_iff.trans hsq_iff.symm
      exact hmeq ▸ hgoal
    · -- m ≤ 1, with 0 < m ⟹ m = 1
      have hm_eq : m = 1 := Nat.le_antisymm hle hm1
      subst hm_eq
      apply iff_of_true
      · decide
      · exact ⟨1, rfl⟩

/-- ★★★ For **odd** `m`: `σ(m) % 2 = 1 ↔ IsSquare m`.  Strong induction on `m`
    via the smallest-prime-power split `m = p^k · m'`. -/
theorem sigma_odd_square_odd : ∀ m, 0 < m → m % 2 = 1 →
    (sigma m % 2 = 1 ↔ IsSquare m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih => exact sigma_odd_square_step m ih

/-! ## §5 — ★★★ FINAL: σ(n) odd ⟺ square or twice-square -/

/-- ★★★ **σ-parity, general**: for `0 < n`,
    `σ(n) % 2 = 1 ↔ ((∃ r, r*r = n) ∨ (∃ r, 2*(r*r) = n))` — σ(n) is odd iff `n`
    is a perfect square or twice a perfect square. -/
theorem sigma_odd_iff {n : Nat} (hn : 0 < n) :
    sigma n % 2 = 1 ↔ ((∃ r, r * r = n) ∨ (∃ r, 2 * (r * r) = n)) := by
  refine (sigma_odd_iff_oddPart hn).trans ?_
  refine (sigma_odd_square_odd (oddPart n) (oddPart_pos hn) (oddPart_odd hn)).trans ?_
  exact (sq_or_twice_iff hn).symm

end E213.Lib.Math.NumberTheory.SigmaParityComplete
