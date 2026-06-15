import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.NumberTheory.DiffPowDvd

/-!
# Jacobsthal-number identities (∅-axiom)

Jacobsthal numbers `J 0 = 0`, `J 1 = 1`, `J (n+2) = J (n+1) + 2·J n`
(`J = 0,1,1,3,5,11,21,43,…`), with:

  * ★ **`sum_pow2`** — `J n + J (n+1) = 2ⁿ` (consecutive Jacobsthals sum to a
    power of two); clean single-step Nat induction.
  * ★★ **`closed_form`** — `3·J n + (−1)ⁿ = 2ⁿ` over `Int`, i.e.
    `J n = (2ⁿ − (−1)ⁿ)/3` (the Jacobsthal closed form); two-step paired
    induction tracking the `(−1)ⁿ` sign (the Pell/Cassini `norm` template).

Genuinely absent *as theorems* — the corpus `JacobsthalCutoff` has the `Jac`
sequence + cut-off tables, but states these two identities only in prose.
A module-local `J` (corpus convention).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.JacobsthalNumbers

open E213.Meta.Int213.PolyIntM (powInt)
open E213.Lib.Math.NumberTheory.DiffPowDvd (ipow ipow_succ)

/-- Jacobsthal sequence: `J 0 = 0`, `J 1 = 1`, `J (n+2) = J (n+1) + 2·J n`. -/
def J : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => J (n + 1) + 2 * J n

/-- Local Nat power of two. -/
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_succ (n : Nat) : pow2 (n + 1) = 2 * pow2 n := rfl

/-- **Jacobsthal recurrence**: `J (n+2) = J (n+1) + 2·J n`. -/
theorem J_rec (n : Nat) : J (n + 2) = J (n + 1) + 2 * J n := rfl

/-- ★ **Jacobsthal sum to a power of two**: `J n + J (n+1) = 2ⁿ`. -/
theorem sum_pow2 (n : Nat) : J n + J (n + 1) = pow2 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show J (k + 1) + J (k + 2) = pow2 (k + 1)
      rw [J_rec k, pow2_succ]
      have e : J (k + 1) + (J (k + 1) + 2 * J k) = 2 * (J k + J (k + 1)) := by ring_nat
      rw [e, ih]

theorem J_rec_cast (n : Nat) :
    ((J (n + 2) : Nat) : Int) = (J (n + 1) : Int) + 2 * (J n : Int) := by
  rw [J_rec n, Int.ofNat_add (J (n + 1)) (2 * J n), Int.ofNat_mul 2 (J n)]; rfl

/-- Paired invariant: closed form at `n` AND `n+1`. -/
theorem closed_form_pair : ∀ n : Nat,
    (3 * (J n : Int) + powInt (-1) n = ipow 2 n)
    ∧ (3 * (J (n + 1) : Int) + powInt (-1) (n + 1) = ipow 2 (n + 1)) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show 3 * (J 0 : Int) + powInt (-1) 0 = ipow 2 0
        rw [show (J 0 : Int) = 0 from rfl]; decide
      · show 3 * (J 1 : Int) + powInt (-1) 1 = ipow 2 1
        rw [show (J 1 : Int) = 1 from rfl]; decide
  | succ k ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      have eJ : ((J (k + 1 + 1) : Nat) : Int)
          = (J (k + 1) : Int) + 2 * (J k : Int) := J_rec_cast k
      show 3 * (J (k + 1 + 1) : Int) + powInt (-1) (k + 1 + 1) = ipow 2 (k + 1 + 1)
      rw [eJ]
      rw [show powInt (-1 : Int) (k + 1 + 1) = powInt (-1) k * (-1) * (-1) from rfl,
          show ipow 2 (k + 1 + 1) = ipow 2 k * 2 * 2 from rfl]
      rw [show ipow 2 (k + 1) = ipow 2 k * 2 from rfl,
          show powInt (-1 : Int) (k + 1) = powInt (-1) k * (-1) from rfl] at ih1
      have key :
          3 * ((J (k + 1) : Int) + 2 * (J k : Int)) + powInt (-1) k * (-1) * (-1)
          = (3 * (J (k + 1) : Int) + powInt (-1) k * (-1))
            + 2 * (3 * (J k : Int) + powInt (-1) k) := by ring_intZ
      rw [key, ih0, ih1]
      ring_intZ

/-- ★ **Jacobsthal closed form**: `3·J n + (−1)ⁿ = 2ⁿ` over `Int`
    (i.e. `J n = (2ⁿ − (−1)ⁿ)/3`). -/
theorem closed_form (n : Nat) :
    3 * (J n : Int) + powInt (-1) n = ipow 2 n :=
  (closed_form_pair n).1

/-! ## Smoke -/

theorem J_5 : J 5 = 11 := by decide
theorem sum_pow2_4 : J 4 + J 5 = 16 := by decide
theorem closed_form_4 : 3 * (J 4 : Int) + 1 = 16 := by decide

end E213.Lib.Math.NumberTheory.JacobsthalNumbers
