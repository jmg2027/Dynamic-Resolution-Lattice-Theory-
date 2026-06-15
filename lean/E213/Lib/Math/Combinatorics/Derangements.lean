import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.OrderMul
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.Combinatorics.Permutations

/-!
# Derangements (subfactorial) — the `±1` one-term recurrence (∅-axiom)

The subfactorial `!n` (number of fixed-point-free permutations) by its two-step
recurrence `!(n+2) = (n+1)·(!(n+1) + !n)`, with the genuine deep theorem:

  ★ **`derange_one_term`**: `(!(n+1) : ℤ) = (n+1)·!n + (−1)^{n+1}` — the famous
    one-term recurrence `D_{n+1} = (n+1)·D_n + (−1)^{n+1}`, the bridge between the
    two-step and one-step forms (proven by induction over `Int` with `powInt`).

  * `derange_le_factorial`: `!n ≤ n!` (derangements are a subset of permutations);
    reuses the corpus factorial `Permutations.fact`.

Entirely absent from the corpus (no `derange`/`subfactorial` previously).
All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.Derangements

open E213.Meta.Int213.PolyIntM (powInt)
open E213.Lib.Math.Combinatorics.Permutations (fact)

/-- Subfactorial `!n` by the two-step recurrence. -/
def derange : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derange (n + 1) + derange n)

/-! ## Concrete values (smoke test) -/

theorem derange_0 : derange 0 = 1 := by decide
theorem derange_1 : derange 1 = 0 := by decide
theorem derange_2 : derange 2 = 1 := by decide
theorem derange_3 : derange 3 = 2 := by decide
theorem derange_4 : derange 4 = 9 := by decide
theorem derange_5 : derange 5 = 44 := by decide
theorem derange_6 : derange 6 = 265 := by decide

/-! ## The one-term `±1` recurrence (the headline)

`(D_{n+1} : ℤ) = (n+1)·D_n + (−1)^{n+1}`. -/

theorem derange_one_term :
    ∀ n : Nat,
      (derange (n + 1) : Int)
        = ((n : Int) + 1) * (derange n : Int) + powInt (-1) (n + 1)
  | 0 => by decide
  | n + 1 => by
      -- LHS, fully cast-pushed
      have hL : (derange (n + 2) : Int)
                  = ((n : Int) + 1)
                    * ((derange (n + 1) : Int) + (derange n : Int)) := by
        show (((n + 1) * (derange (n + 1) + derange n) : Nat) : Int)
              = ((n : Int) + 1)
                * ((derange (n + 1) : Int) + (derange n : Int))
        rw [Int.ofNat_mul, Int.ofNat_add]
        rfl
      have ih := derange_one_term n
      have hp : powInt (-1) (n + 2) = powInt (-1) (n + 1) * (-1) := rfl
      show (derange (n + 2) : Int)
            = (((n + 1 : Nat) : Int) + 1) * (derange (n + 1) : Int)
              + powInt (-1) (n + 2)
      rw [hL, hp, ih]
      have hc : (((n + 1 : Nat) : Int)) = (n : Int) + 1 := rfl
      rw [hc]
      ring_intZ

/-! ## Bound `!n ≤ n!` -/

/-- `derange n ≤ fact n` — derangements are a subset of all permutations. -/
theorem derange_le_factorial :
    ∀ n : Nat, derange n ≤ fact n
  | 0 => Nat.le_refl 1
  | 1 => Nat.zero_le _
  | n + 2 => by
      show (n + 1) * (derange (n + 1) + derange n)
            ≤ (n + 2) * fact (n + 1)
      have h1 : derange (n + 1) ≤ fact (n + 1) := derange_le_factorial (n + 1)
      have h2 : derange n ≤ fact n := derange_le_factorial n
      have hf1 : fact (n + 1) = (n + 1) * fact n := rfl
      have hsum : derange (n + 1) + derange n ≤ (n + 2) * fact n := by
        have hb : derange (n + 1) + derange n ≤ fact (n + 1) + fact n :=
          Nat.add_le_add h1 h2
        have he : fact (n + 1) + fact n = (n + 2) * fact n := by
          rw [hf1]; ring_nat
        rw [he] at hb
        exact hb
      have step1 : (n + 1) * (derange (n + 1) + derange n)
                    ≤ (n + 1) * ((n + 2) * fact n) :=
        Nat.mul_le_mul_left _ hsum
      have hcomm : (n + 1) * ((n + 2) * fact n) = (n + 2) * fact (n + 1) := by
        rw [hf1]; ring_nat
      rw [hcomm] at step1
      exact step1

end E213.Lib.Math.Combinatorics.Derangements
