import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList
import E213.Lib.Math.NumberTheory.PolyRoot.RootBound
import E213.Lib.Math.NumberTheory.PolyRoot.CyclotomicPoly
import E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
import E213.Meta.Nat.PolyNatMTactic

/-!
# ModArith/NonFixedExists — a non-cube-fixed element exists (Lagrange ⟹ Pillar I existence)

Given `p` prime with `p − 1 = 3m`, Lagrange's root bound forces some nonzero residue `a` with
`aᵐ ≢ 1 (mod p)`: otherwise all `p−1` distinct residues would be roots of `Tᵐ − 1`, but that
polynomial has length `m+1 ≤ p−1`, so `eval_zero` would force its constant coefficient `−1` to
be `≡ 0 (mod p)` — impossible.

The witness is produced **constructively** by a bounded search `firstNonFixed` (pure `Nat`
decision), whose `none`-branch is refuted by the Lagrange contradiction.

  * `firstNonFixed` — search `1 … bound` for `aᵐ % p ≠ 1`.
  * ★★★ `exists_nonfixed` — `∃ a, 1 ≤ a ∧ a < p ∧ aᵐ % p ≠ 1`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.NonFixedExists

open E213.Lib.Math.NumberTheory.PolyRoot
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (dvd_sub_one_of_mod_one one_le_pow')
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- `(↑(m·n) : Int) = ↑m · ↑n`. -/
theorem natCast_mul (m n : Nat) : ((m * n : Nat) : Int) = (m : Int) * (n : Int) := rfl

/-- `(↑(aᵐ) : Int) = (↑a)ᵐ` (pure replacement for `Int.natCast_pow`). -/
theorem natCast_pow (a : Nat) : ∀ m, ((a ^ m : Nat) : Int) = (a : Int) ^ m
  | 0 => by rw [Nat.pow_zero, Int.pow_zero]; rfl
  | m + 1 => by rw [Nat.pow_succ, Int.pow_succ, natCast_mul, natCast_pow]

/-- `1 ≤ x` ⟹ `(↑(x−1) : Int) = ↑x − 1`. -/
theorem natCast_sub_one (x : Nat) (h : 1 ≤ x) : ((x - 1 : Nat) : Int) = (x : Int) - 1 := by
  have hx : (x - 1) + 1 = x := E213.Tactic.NatHelper.sub_add_cancel h
  have hc : ((x - 1 : Nat) : Int) + 1 = (x : Int) := by rw [← natCast_succ, hx]
  rw [← hc]; ring_intZ

/-- Search `bound, bound−1, …, 1` for the first `a` with `aᵐ % p ≠ 1`. -/
def firstNonFixed (p m : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 => if (k + 1) ^ m % p = 1 then firstNonFixed p m k else some (k + 1)

/-- A `some`-result is a genuine non-fixed witness in `[1, bound]`. -/
theorem firstNonFixed_some (p m : Nat) : ∀ (bound a : Nat),
    firstNonFixed p m bound = some a → 1 ≤ a ∧ a ≤ bound ∧ a ^ m % p ≠ 1 := by
  intro bound
  induction bound with
  | zero => intro a h; exact Option.noConfusion h
  | succ k ih =>
    intro a h
    rw [firstNonFixed] at h
    by_cases hc : (k + 1) ^ m % p = 1
    · rw [if_pos hc] at h
      obtain ⟨h1, h2, h3⟩ := ih a h
      exact ⟨h1, Nat.le_succ_of_le h2, h3⟩
    · rw [if_neg hc] at h
      have ha : k + 1 = a := Option.some.inj h
      subst ha
      exact ⟨Nat.succ_pos k, Nat.le_refl _, hc⟩

/-- A `none`-result means every residue in `[1, bound]` is fixed by `·ᵐ`. -/
theorem firstNonFixed_none (p m : Nat) : ∀ (bound : Nat),
    firstNonFixed p m bound = none → ∀ a, 1 ≤ a → a ≤ bound → a ^ m % p = 1 := by
  intro bound
  induction bound with
  | zero => intro _ a h1 h2; exact absurd (Nat.le_trans h1 h2) (by decide)
  | succ k ih =>
    intro h a h1 h2
    rw [firstNonFixed] at h
    by_cases hc : (k + 1) ^ m % p = 1
    · rw [if_pos hc] at h
      rcases Nat.lt_or_eq_of_le h2 with hlt | heq
      · exact ih h a h1 (Nat.le_of_lt_succ hlt)
      · subst heq; exact hc
    · rw [if_neg hc] at h
      exact Option.noConfusion h

/-- ★★★ **A non-cube-fixed element exists.**  `p` prime, `p − 1 = 3m` ⟹
    `∃ a, 1 ≤ a ∧ a < p ∧ aᵐ % p ≠ 1`. -/
theorem exists_nonfixed (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hm : 3 * m = p - 1) : ∃ a : Nat, 1 ≤ a ∧ a < p ∧ a ^ m % p ≠ 1 := by
  -- m ≥ 1
  have hp1 : 1 ≤ p - 1 := E213.Tactic.NatHelper.le_sub_of_add_le hp
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hm; rw [← hm] at hp1; exact absurd hp1 (by decide)
    · exact h0
  have hm1eq : (m - 1) + 1 = m := E213.Tactic.NatHelper.sub_add_cancel hm1
  -- search the residues [1, p-1]
  cases hfn : firstNonFixed p m (p - 1) with
  | some a =>
      obtain ⟨h1, h2, h3⟩ := firstNonFixed_some p m (p - 1) a hfn
      exact ⟨a, h1, Nat.lt_of_le_of_lt h2 (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) hp) (by decide)), h3⟩
  | none =>
      exfalso
      have hall := firstNonFixed_none p m (p - 1) hfn
      -- the residue list and its properties
      have hone : 1 + (p - 1) = p := E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hp)
      have hroots : ∀ r ∈ intRangeFrom ((1 : Nat) : Int) (p - 1),
          (p : Int) ∣ eval (pmoSucc (m - 1)) r := by
        intro r hr
        obtain ⟨a, h1a, hap, hra⟩ := mem_intRangeFrom_nat (p - 1) 1 hr
        rw [hone] at hap
        have hap' : a ≤ p - 1 := E213.Tactic.NatHelper.le_sub_of_add_le hap
        have hfix : a ^ m % p = 1 := hall a h1a hap'
        have hdvdnat : p ∣ a ^ m - 1 := dvd_sub_one_of_mod_one p (a ^ m) hfix
        have heval : eval (pmoSucc (m - 1)) r = (a : Int) ^ m - 1 := by
          rw [hra, eval_pmoSucc, hm1eq]
        rw [heval, ← natCast_pow, ← natCast_sub_one (a ^ m) (one_le_pow' a h1a m)]
        exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact hdvdnat)
      have hdist := intRangeFrom_pairwise p (p - 1) 1 (Nat.sub_le p 1)
      -- length bound: (m-1)+2 = m+1 ≤ p-1 = 3m
      have hmm : (m - 1) + 2 = m + 1 := by
        rw [show (2 : Nat) = 1 + 1 from rfl, ← Nat.add_assoc, hm1eq]
      have hle : m + 1 ≤ 3 * m := by
        have ht : m + 2 * m = 3 * m := by ring_nat
        have h2m : 1 ≤ 2 * m := Nat.le_trans hm1 (Nat.le_mul_of_pos_left m (by decide))
        calc m + 1 ≤ m + 2 * m := Nat.add_le_add_left h2m m
          _ = 3 * m := ht
      have hlen : (pmoSucc (m - 1)).length ≤ (intRangeFrom ((1 : Nat) : Int) (p - 1)).length := by
        rw [pmoSucc_length, intRangeFrom_length, hmm, ← hm]; exact hle
      have hvanish := eval_zero p hp hpr (pmoSucc (m - 1)).length (pmoSucc (m - 1))
        (Nat.le_refl _) (intRangeFrom ((1 : Nat) : Int) (p - 1)) hdist hroots hlen 0
      rw [eval_pmoSucc_zero] at hvanish
      -- (p : Int) ∣ -1 ⟹ p ≤ 1, contradiction
      have hd1 : p ∣ Int.natAbs (-1) := int_dvd_to_nat p (-1) hvanish
      have hple : p ≤ 1 := le_of_dvd_pos p (Int.natAbs (-1)) (by decide) hd1
      exact absurd hple (Nat.not_le.mpr hp)

end E213.Lib.Math.NumberTheory.ModArith.NonFixedExists
