import E213.Lib.Math.NumberTheory.FibZIdentities
import E213.Lib.Math.NumberTheory.DyadicFSM.FibApparitionMod5
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# The 5-adic valuation law `ν₅(F_n) = ν₅(n)`

Closes the open lifting-the-exponent rung of `G124_padic_drlt_5adic.md`.
Stated over a native `Nat` Fibonacci `fibN` as

  `∀ n k, 5ᵏ ∣ F_n ⟺ 5ᵏ ∣ n`

(equivalently `ν₅(F_n) = ν₅(n)`, both finite for `n ≥ 1`).

The engine is the quintupling identity `fibZ_quintuple_factored`
(`F_{5m} = 5·C_m·F_m`, `C_m ≡ 1 mod 5`) bridged to `fibN`; the cancellation
uses Euclid for the prime `5` (`IntEuclid.int_euclid`,
`MarkovPrimeFactor.euclid_of_coprime` + `dvd_prime_pow_cases`).
-/

namespace E213.Lib.Math.NumberTheory.FibZValuation

open E213.Lib.Math.Analysis.Cauchy.OrbitDimension (fibZ)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign)
open E213.Lib.Math.NumberTheory.FibZIdentities (fibZ_quintuple_factored)
open E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod5 (fibFSMmod5)
open E213.Lib.Math.NumberTheory.DyadicFSM.FibApparitionMod5 (fibMod5 fibMod5_zero_iff)
open E213.Lib.Math.NumberTheory.PolyRoot (natAbs_mul nat_dvd_to_int int_dvd_to_nat dvd_sub')
open E213.Meta.Nat.AddMod213 (add_mod_gen dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
  (le_of_dvd_loc euclid_of_coprime dvd_prime_pow_cases)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right)
open E213.Tactic.NatHelper (gcd213 mul_mod_right)

/-! ## Native `Nat` Fibonacci and its cast -/

/-- Native `Nat` Fibonacci. -/
def fibN : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibN (n + 1) + fibN n

private theorem fibN_cast_pair (n : Nat) :
    ((fibN n : Int) = fibZ n) ∧ ((fibN (n + 1) : Int) = fibZ (n + 1)) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show ((fibN (k + 1) + fibN k : Nat) : Int) = fibZ (k + 2)
    rw [show fibZ (k + 2) = fibZ (k + 1) + fibZ k from rfl, ← h1, ← h2]
    rfl

theorem fibN_cast (n : Nat) : (fibN n : Int) = fibZ n := (fibN_cast_pair n).1

theorem fibN_natAbs (n : Nat) : (fibZ n).natAbs = fibN n := by
  rw [← fibN_cast n]; exact Int.natAbs_ofNat (fibN n)

/-! ## Rank of apparition over `fibN` (FSM bridge) -/

private theorem run_val (n : Nat) :
    (fibFSMmod5.run n).1.val = fibN n % 5
    ∧ (fibFSMmod5.run n).2.val = fibN (n + 1) % 5 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    show ((fibFSMmod5.run k).1.val + (fibFSMmod5.run k).2.val) % 5 = fibN (k + 2) % 5
    rw [h1, h2, ← add_mod_gen,
        show fibN (k + 2) = fibN (k + 1) + fibN k from rfl, Nat.add_comm (fibN k)]

private theorem fibMod5_eq (n : Nat) : fibMod5 n = fibN n % 5 := (run_val n).1

private theorem mod_eq_zero_of_dvd_five {a : Nat} (h : 5 ∣ a) : a % 5 = 0 := by
  obtain ⟨q, hq⟩ := h; rw [hq]; exact E213.Tactic.NatHelper.mul_mod_right 5 q

/-- **Rank of apparition over `fibN`**: `5 ∣ F_n ⟺ 5 ∣ n`. -/
theorem five_dvd_fibN (n : Nat) : 5 ∣ fibN n ↔ 5 ∣ n := by
  constructor
  · intro h
    have hm : fibN n % 5 = 0 := mod_eq_zero_of_dvd_five h
    have : fibMod5 n = 0 := by rw [fibMod5_eq]; exact hm
    exact dvd_of_mod_eq_zero ((fibMod5_zero_iff n).mp this)
  · intro h
    have hn : n % 5 = 0 := mod_eq_zero_of_dvd_five h
    have hf : fibMod5 n = 0 := (fibMod5_zero_iff n).mpr hn
    rw [fibMod5_eq] at hf
    exact dvd_of_mod_eq_zero hf

/-! ## The cofactor and the quintupling bridge to `fibN` -/

/-- The Int cofactor `C_m = 5F_m⁴ + 5(−1)ᵐF_m² + 1`. -/
private def cofZ (m : Nat) : Int :=
  5 * (fibZ m * fibZ m * fibZ m * fibZ m) + 5 * altSign m * (fibZ m * fibZ m) + 1

/-- Nat cofactor `c_m = |C_m|`. -/
def cofN (m : Nat) : Nat := (cofZ m).natAbs

private theorem not_five_dvd_one : ¬ ((5 : Int) ∣ 1) := by
  intro h
  have : (5 : Nat) ∣ (1 : Int).natAbs := int_dvd_to_nat 5 1 h
  have h1 : (5 : Nat) ∣ 1 := this
  exact absurd (le_of_dvd_loc (by decide) h1) (by decide)

private theorem not_five_dvd_cofZ (m : Nat) : ¬ ((5 : Int) ∣ cofZ m) := by
  intro h
  have hsub : (5 : Int) ∣ (cofZ m - 1) :=
    ⟨fibZ m * fibZ m * fibZ m * fibZ m + altSign m * (fibZ m * fibZ m), by
      show cofZ m - 1 = 5 * _
      unfold cofZ; ring_intZ⟩
  exact not_five_dvd_one (by
    have := dvd_sub' h hsub
    rwa [show cofZ m - (cofZ m - 1) = 1 from by ring_intZ] at this)

/-- `5 ∤ c_m`. -/
theorem not_five_dvd_cofN (m : Nat) : ¬ (5 ∣ cofN m) := by
  intro h
  exact not_five_dvd_cofZ m (nat_dvd_to_int 5 (cofZ m) h)

/-- **Quintupling over `fibN`**: `F_{5m} = 5·c_m·F_m`, `5 ∤ c_m`. -/
theorem fibN_quintuple (m : Nat) :
    fibN (m + m + m + m + m) = 5 * cofN m * fibN m := by
  have h := fibZ_quintuple_factored m
  have hb : fibN (m + m + m + m + m) = (fibZ (m + m + m + m + m)).natAbs :=
    (fibN_natAbs _).symm
  rw [hb, h]
  -- (5 * (cofZ m * fibZ m)).natAbs = 5 * cofN m * fibN m
  show (5 * (cofZ m * fibZ m)).natAbs = 5 * cofN m * fibN m
  rw [natAbs_mul, natAbs_mul, fibN_natAbs]
  show (5 : Int).natAbs * ((cofZ m).natAbs * fibN m) = 5 * cofN m * fibN m
  rw [show (5 : Int).natAbs = 5 from rfl, E213.Tactic.NatHelper.mul_assoc]
  rfl

/-! ## The lifting-the-exponent step (Nat) -/

private theorem mod_zero_of_dvd_gen {d a : Nat} (h : d ∣ a) : a % d = 0 := by
  obtain ⟨c, hc⟩ := h; rw [hc]; exact mul_mod_right d c

private theorem dvd_trans_nat {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨u, hu⟩ := h1; obtain ⟨v, hv⟩ := h2
  exact ⟨u * v, by rw [hv, hu, E213.Tactic.NatHelper.mul_assoc]⟩

private theorem dvd_zero_nat (a : Nat) : a ∣ 0 := ⟨0, (Nat.mul_zero a).symm⟩

private theorem five_mul (m : Nat) : 5 * m = m + m + m + m + m := by ring_nat

private theorem mul_cancel5 {B C : Nat} (h : 5 * B = 5 * C) : B = C :=
  Nat.le_antisymm
    (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h) (by decide))
    (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h.symm) (by decide))

private theorem five_mul_dvd_iff {A B : Nat} : 5 * A ∣ 5 * B ↔ A ∣ B := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    exact ⟨t, mul_cancel5 (by rw [ht, E213.Tactic.NatHelper.mul_assoc])⟩
  · intro h
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by rw [ht, E213.Tactic.NatHelper.mul_assoc]⟩

private theorem dvd_mul_left_nat {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ c * b := by
  obtain ⟨t, ht⟩ := h; exact ⟨c * t, by rw [ht]; ring_nat⟩

private theorem hpr5_aux : ∀ d, d < 6 → 5 % d = 0 → d = 1 ∨ d = 5 := by decide

private theorem hpr5 (d : Nat) (hd : d ∣ 5) : d = 1 ∨ d = 5 :=
  hpr5_aux d (Nat.lt_succ_of_le (le_of_dvd_loc (by decide) hd)) (mod_zero_of_dvd_gen hd)

/-- `5 ∤ c ⟹ gcd(c, 5ʲ) = 1`. -/
private theorem gcd_cofN_pow {c : Nat} (hc : ¬ 5 ∣ c) (j : Nat) :
    gcd213 c (5 ^ j) = 1 := by
  rcases dvd_prime_pow_cases 5 (by decide) hpr5 j (gcd213 c (5 ^ j))
      (gcd213_dvd_right c (5 ^ j)) with h1 | h5
  · exact h1
  · exact absurd (dvd_trans_nat h5 (gcd213_dvd_left c (5 ^ j))) hc

/-- **Coprime cancellation**: `5 ∤ c ⟹ (5ʲ ∣ c·x ⟺ 5ʲ ∣ x)`. -/
private theorem cop_cancel {c x : Nat} (hc : ¬ 5 ∣ c) (j : Nat) :
    5 ^ j ∣ c * x ↔ 5 ^ j ∣ x := by
  constructor
  · intro h
    cases j with
    | zero => exact Nat.one_dvd x
    | succ i =>
      have h1j : 1 < 5 ^ (i + 1) :=
        Nat.lt_of_lt_of_le (show (1 : Nat) < 5 from by decide)
          (by rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left 5 (Nat.pos_pow_of_pos i (by decide)))
      exact euclid_of_coprime c x (5 ^ (i + 1)) h1j (gcd_cofN_pow hc (i + 1)) h
  · intro h; exact dvd_mul_left_nat h c

private theorem five_dvd_five_pow_succ (j : Nat) : 5 ∣ 5 ^ (j + 1) :=
  ⟨5 ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩

/-- The lift on the Fibonacci side: `5^{j+1} ∣ F_{5m} ⟺ 5ʲ ∣ F_m`. -/
private theorem lift (m j : Nat) :
    5 ^ (j + 1) ∣ fibN (m + m + m + m + m) ↔ 5 ^ j ∣ fibN m := by
  have e1 : fibN (m + m + m + m + m) = 5 * (cofN m * fibN m) := by
    rw [fibN_quintuple m, E213.Tactic.NatHelper.mul_assoc]
  have e2 : (5 : Nat) ^ (j + 1) = 5 * 5 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [e1, e2]
  exact five_mul_dvd_iff.trans (cop_cancel (not_five_dvd_cofN m) j)

/-- The lift on the index side: `5^{j+1} ∣ 5m ⟺ 5ʲ ∣ m`. -/
private theorem lift_index (m j : Nat) : 5 ^ (j + 1) ∣ 5 * m ↔ 5 ^ j ∣ m := by
  rw [show (5 : Nat) ^ (j + 1) = 5 * 5 ^ j from by rw [Nat.pow_succ, Nat.mul_comm]]
  exact five_mul_dvd_iff

/-! ## The valuation law -/

/-- **`ν₅(F_n) = ν₅(n)`** in divisibility form: `5ᵏ ∣ F_n ⟺ 5ᵏ ∣ n` for
    every `n, k`.  The all-orders lifting-the-exponent law at the ramified
    prime `5`. -/
theorem fibN_val_law (n : Nat) : ∀ k, 5 ^ k ∣ fibN n ↔ 5 ^ k ∣ n :=
  Nat.strongRecOn n (motive := fun n => ∀ k, 5 ^ k ∣ fibN n ↔ 5 ^ k ∣ n)
    (fun n ih k => by
      rcases Nat.eq_zero_or_pos (n % 5) with h5 | h5
      · -- 5 ∣ n
        have hdvd : 5 ∣ n := dvd_of_mod_eq_zero h5
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          exact ⟨fun _ => dvd_zero_nat _, fun _ => dvd_zero_nat _⟩
        · obtain ⟨m, hm⟩ := hdvd
          have hmpos : 0 < m := by
            rcases Nat.eq_zero_or_pos m with h | h
            · subst h; rw [Nat.mul_zero] at hm; subst hm
              exact absurd hnpos (Nat.lt_irrefl 0)
            · exact h
          have hmn : m < n := by
            rw [hm, five_mul]
            have hpos4 : 0 < m + m + m + m :=
              Nat.lt_of_lt_of_le hmpos (Nat.le_add_left m (m + m + m))
            exact Nat.lt_add_of_pos_left hpos4
          cases k with
          | zero => exact ⟨fun _ => Nat.one_dvd n, fun _ => Nat.one_dvd (fibN n)⟩
          | succ j =>
            calc 5 ^ (j + 1) ∣ fibN n
                ↔ 5 ^ (j + 1) ∣ fibN (m + m + m + m + m) := by
                    rw [show fibN n = fibN (m + m + m + m + m) from by rw [hm, five_mul]]
              _ ↔ 5 ^ j ∣ fibN m := lift m j
              _ ↔ 5 ^ j ∣ m := ih m hmn j
              _ ↔ 5 ^ (j + 1) ∣ 5 * m := (lift_index m j).symm
              _ ↔ 5 ^ (j + 1) ∣ n := by rw [hm]
      · -- 5 ∤ n
        have hn5 : ¬ 5 ∣ n := fun h => Nat.lt_irrefl 0 (mod_zero_of_dvd_gen h ▸ h5)
        have hf5 : ¬ 5 ∣ fibN n := fun h => hn5 ((five_dvd_fibN n).mp h)
        cases k with
        | zero => exact ⟨fun _ => Nat.one_dvd n, fun _ => Nat.one_dvd (fibN n)⟩
        | succ j =>
          exact ⟨fun h => absurd (dvd_trans_nat (five_dvd_five_pow_succ j) h) hf5,
                 fun h => absurd (dvd_trans_nat (five_dvd_five_pow_succ j) h) hn5⟩)

end E213.Lib.Math.NumberTheory.FibZValuation
