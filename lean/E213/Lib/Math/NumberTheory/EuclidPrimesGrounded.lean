import E213.Lib.Math.NumberTheory.MulDescentGroundedNoDiv

/-!
# Euclid's infinitude of primes — `lt_wfRel`-free, grounded (∅-axiom)

A *second* deep-discipline clearance on the descent leg, showing the `Nat.div`/`Nat.mod`-free
grounding generalises beyond FTA existence.  Euclid's theorem — no finite list contains every prime —
reuses the clean `minFac'` (divisibility by structural subtraction, `MulDescentGroundedNoDiv`): for
any list `L` of primes, `N = prodL L + 1` has a prime factor `minFac' N` not in `L` (each `p ∈ L`
divides `prodL L` and `N`, hence `N - prodL L = 1`, forcing `p ≤ 1`, contra `p ≥ 2`).

`infinitude_of_primes` carries **no `Nat.div`, no `Nat.mod`, no `Nat.strongRecOn`, no
`Nat.lt_wfRel`** — division rebuilt from `Nat.sub`, the prime-factor search grounded throughout.
∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.EuclidPrimesGrounded

open E213.Lib.Math.NumberTheory.PrimeFactorization (prodL prodL_cons le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.MulDescentGroundedNoDiv (minFac' minFac'_spec minFac'_prime)
open E213.Meta.Nat.SubMod213 (le_add_cancel_left)

/-! ## §1 — clean divisibility helpers (no propext / no `Nat.div`) -/

/-- Transitivity of `∣`, propext-free (core `Nat.dvd_trans` leaks propext). -/
theorem dvd_trans' {p q r : Nat} (h1 : p ∣ q) (h2 : q ∣ r) : p ∣ r := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨a * b, by rw [hb, ha]; exact E213.Tactic.NatHelper.mul_assoc p a b⟩

/-- `(a + 1) - a = 1`, propext-free (core `Nat.add_sub_cancel` leaks propext). -/
theorem add_one_sub_self : ∀ a : Nat, (a + 1) - a = 1
  | 0 => rfl
  | a + 1 => by rw [Nat.succ_sub_succ]; exact add_one_sub_self a

/-- A positive-element list has positive product. -/
theorem prodL_pos : ∀ (L : List Nat), (∀ q, q ∈ L → 0 < q) → 0 < prodL L
  | [],      _ => by decide
  | x :: xs, h => by
    rw [prodL_cons]
    exact Nat.mul_pos (h x (List.Mem.head xs))
      (prodL_pos xs (fun q hq => h q (List.Mem.tail x hq)))

/-- Every list member divides the product. -/
theorem mem_dvd_prodL : ∀ {L : List Nat} {q : Nat}, q ∈ L → q ∣ prodL L
  | x :: xs, q, h => by
    rw [prodL_cons]
    cases h with
    | head => exact Nat.dvd_mul_right x (prodL xs)
    | tail _ h' => exact dvd_trans' (mem_dvd_prodL h') (Nat.dvd_mul_left (prodL xs) x)

/-! ## §2 — Euclid: no finite list contains every prime -/

/-- ★★★ **Euclid's infinitude of primes, grounded.**  For any list `L` of primes there is a prime
    not in `L` — `minFac' (prodL L + 1)`.  Reuses the `Nat.mod`-free `minFac'`; carries no `Nat.div`,
    `Nat.mod`, `Nat.strongRecOn`, or `Nat.lt_wfRel`.  The second deep-discipline clearance on the
    descent leg, ∅-axiom. -/
theorem infinitude_of_primes (L : List Nat) (hL : ∀ q, q ∈ L → Prime213 q) :
    ∃ p, Prime213 p ∧ p ∉ L := by
  have hpos : 0 < prodL L := prodL_pos L (fun q hq =>
    Nat.lt_of_lt_of_le (by decide) (hL q hq).1)
  have hN2 : 2 ≤ prodL L + 1 := Nat.succ_le_succ hpos
  let p := minFac' (prodL L + 1)
  refine ⟨p, minFac'_prime hN2, ?_⟩
  intro hpL
  obtain ⟨hp2, _⟩ := minFac'_prime hN2
  obtain ⟨_, hp_dvd, _, _⟩ := minFac'_spec hN2
  obtain ⟨a, ha⟩ := hp_dvd                       -- prodL L + 1 = p * a
  obtain ⟨b, hb⟩ := mem_dvd_prodL hpL            -- prodL L = p * b
  -- p * a = p * b + 1
  have hab : p * a = p * b + 1 := by rw [← hb]; exact ha.symm
  -- b < a (else p*a ≤ p*b < p*a)
  have hba : b + 1 ≤ a := Nat.lt_of_not_le (fun hab' =>
    Nat.lt_irrefl (p * a)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl p) hab')
        (hab ▸ Nat.lt_succ_self (p * b))))
  -- p*b + p ≤ p*a = p*b + 1  ⟹  p ≤ 1
  have hstep : p * b + p ≤ p * b + 1 := by
    have h1 : p * (b + 1) ≤ p * a := Nat.mul_le_mul (Nat.le_refl p) hba
    rw [Nat.mul_succ] at h1
    rw [← hab]; exact h1
  have hp_le : p ≤ 1 := le_add_cancel_left (p * b) hstep
  exact absurd hp_le (Nat.not_le_of_lt (Nat.lt_of_lt_of_le (by decide) hp2))

end E213.Lib.Math.NumberTheory.EuclidPrimesGrounded
