import E213.Meta.Int213.PolyIntM
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core
import E213.Meta.Int213.Order

/-!
# Generalized Lucas sequences `U_n(P,Q)`, `V_n(P,Q)` over `Int` (∅-axiom)
-/

namespace E213.ScratchLUCS.Proof

open E213.Meta.Int213.PolyIntM (powInt powInt_add mul_zeroZ)
open E213.Meta.Int213
  (mul_neg mul_one neg_mul mul_assoc mul_comm mul_left_comm mul_sub sub_mul
   add_mul mul_add zero_mul int_eq_zero_of_mul_left)
open E213.Meta.Int213.Order (eq_of_sub_eq_zero sub_self_zero)

/-! ## §0 — PURE `Int` left-cancellation -/

/-- `x ≠ 0 → x·a = x·b → a = b` over `Int`, PURE (no `propext`).  Built from
    `int_eq_zero_of_mul_left` + `eq_of_sub_eq_zero` + `mul_sub`. -/
theorem mulCancelL {x a b : Int} (hx : x ≠ 0) (h : x * a = x * b) : a = b := by
  apply eq_of_sub_eq_zero
  apply int_eq_zero_of_mul_left hx
  rw [mul_sub, h, sub_self_zero]

/-! ## §1 — window definition -/

/-- **Lucas window**: `lucWindow P Q n = (U n, U(n+1), V n, V(n+1))`. -/
def lucWindow (P Q : Int) : Nat → Int × Int × Int × Int
  | 0 => (0, 1, 2, P)
  | n + 1 =>
      let w := lucWindow P Q n
      (w.2.1, P * w.2.1 - Q * w.1, w.2.2.2, P * w.2.2.2 - Q * w.2.2.1)

/-- `U n`: Lucas sequence of the first kind. -/
def lucU (P Q : Int) (n : Nat) : Int := (lucWindow P Q n).1
/-- `V n`: Lucas sequence of the second kind. -/
def lucV (P Q : Int) (n : Nat) : Int := (lucWindow P Q n).2.2.1
/-- Discriminant `D = P² − 4Q`. -/
def lucD (P Q : Int) : Int := P * P - 4 * Q

/-! ## §2 — window-tail identification + recurrences -/

theorem lucWindow_tail (P Q : Int) (n : Nat) :
    (lucWindow P Q n).2.1 = lucU P Q (n + 1)
    ∧ (lucWindow P Q n).2.2.2 = lucV P Q (n + 1) :=
  ⟨rfl, rfl⟩

theorem lucU_tail (P Q : Int) (n : Nat) :
    (lucWindow P Q n).2.1 = lucU P Q (n + 1) := (lucWindow_tail P Q n).1
theorem lucV_tail (P Q : Int) (n : Nat) :
    (lucWindow P Q n).2.2.2 = lucV P Q (n + 1) := (lucWindow_tail P Q n).2

theorem lucU_zero (P Q : Int) : lucU P Q 0 = 0 := rfl
theorem lucU_one  (P Q : Int) : lucU P Q 1 = 1 := rfl
theorem lucV_zero (P Q : Int) : lucV P Q 0 = 2 := rfl
theorem lucV_one  (P Q : Int) : lucV P Q 1 = P := rfl

/-- `U (n+2) = P · U(n+1) − Q · U n`. -/
theorem lucU_rec (P Q : Int) (n : Nat) :
    lucU P Q (n + 2) = P * lucU P Q (n + 1) - Q * lucU P Q n := by
  show (lucWindow P Q (n + 1)).2.1 = P * lucU P Q (n + 1) - Q * lucU P Q n
  show P * (lucWindow P Q n).2.1 - Q * (lucWindow P Q n).1
      = P * lucU P Q (n + 1) - Q * lucU P Q n
  rw [lucU_tail]; rfl

/-- `V (n+2) = P · V(n+1) − Q · V n`. -/
theorem lucV_rec (P Q : Int) (n : Nat) :
    lucV P Q (n + 2) = P * lucV P Q (n + 1) - Q * lucV P Q n := by
  show (lucWindow P Q (n + 1)).2.2.2 = P * lucV P Q (n + 1) - Q * lucV P Q n
  show P * (lucWindow P Q n).2.2.2 - Q * (lucWindow P Q n).2.2.1
      = P * lucV P Q (n + 1) - Q * lucV P Q n
  rw [lucV_tail]; rfl

/-! ## §3 — cross identities (simultaneous induction)

`2 U(n+1) = P U n + V n`  and  `2 V(n+1) = D U n + P V n`. -/

theorem cross_U_kernel (P Q u0 u1 v0 v1 : Int)
    (hA : 2 * u1 = P * u0 + v0) (hB : 2 * v1 = (P * P - 4 * Q) * u0 + P * v0) :
    2 * (P * u1 - Q * u0) = P * u1 + v1 := by
  apply mulCancelL (a := 2 * (P * u1 - Q * u0)) (b := P * u1 + v1)
    (show (2 : Int) ≠ 0 by decide)
  rw [mul_add 2 (P * u1) v1, hB]
  have hv0 : v0 = 2 * u1 - P * u0 := by rw [hA]; ring_intZ
  rw [hv0]; ring_intZ

theorem cross_V_kernel (P Q u0 u1 v0 v1 : Int)
    (hA : 2 * u1 = P * u0 + v0) (hB : 2 * v1 = (P * P - 4 * Q) * u0 + P * v0) :
    2 * (P * v1 - Q * v0) = (P * P - 4 * Q) * u1 + P * v1 := by
  apply mulCancelL (a := 2 * (P * v1 - Q * v0))
    (b := (P * P - 4 * Q) * u1 + P * v1) (show (2 : Int) ≠ 0 by decide)
  -- expose `2 * v1` by pulling the scalar past `P`
  rw [mul_add 2 ((P * P - 4 * Q) * u1) (P * v1), mul_left_comm 2 P v1, hB]
  have hv0 : v0 = 2 * u1 - P * u0 := by rw [hA]; ring_intZ
  rw [hv0]; ring_intZ

theorem lucUV_cross (P Q : Int) (n : Nat) :
    2 * lucU P Q (n + 1) = P * lucU P Q n + lucV P Q n
    ∧ 2 * lucV P Q (n + 1) = (P * P - 4 * Q) * lucU P Q n + P * lucV P Q n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [lucU_one, lucU_zero, lucV_zero, mul_zeroZ]
      show (2 : Int) * 1 = 0 + 2; ring_intZ
    · rw [lucV_one, lucU_zero, lucV_zero, mul_zeroZ]
      show (2 : Int) * P = 0 + P * 2; ring_intZ
  | succ k ih =>
    obtain ⟨ihA, ihB⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [lucU_rec]
      exact cross_U_kernel P Q (lucU P Q k) (lucU P Q (k + 1))
        (lucV P Q k) (lucV P Q (k + 1)) ihA ihB
    · rw [lucV_rec]
      exact cross_V_kernel P Q (lucU P Q k) (lucU P Q (k + 1))
        (lucV P Q k) (lucV P Q (k + 1)) ihA ihB

theorem lucUV_cross_U (P Q : Int) (n : Nat) :
    2 * lucU P Q (n + 1) = P * lucU P Q n + lucV P Q n := (lucUV_cross P Q n).1
theorem lucUV_cross_V (P Q : Int) (n : Nat) :
    2 * lucV P Q (n + 1) = (P * P - 4 * Q) * lucU P Q n + P * lucV P Q n :=
  (lucUV_cross P Q n).2

/-! ## §4 — the fundamental quadratic relation `V² − D U² = 4 Qⁿ` -/

theorem powInt_succ' (Q : Int) (n : Nat) : powInt Q (n + 1) = powInt Q n * Q := rfl

/-- Step kernel: `N(k+1) = Q · N(k)`, via `4·N(k+1) = (2V)² − D(2U)² = 4Q·N(k)`. -/
theorem quad_kernel (P Q u0 u1 v0 v1 : Int)
    (hA : 2 * u1 = P * u0 + v0) (hB : 2 * v1 = (P * P - 4 * Q) * u0 + P * v0) :
    v1 * v1 - (P * P - 4 * Q) * (u1 * u1)
      = Q * (v0 * v0 - (P * P - 4 * Q) * (u0 * u0)) := by
  apply mulCancelL (show (4 : Int) ≠ 0 by decide)
  -- 4 * N(k+1) = 4 * (Q * N(k))
  have h : (2 * v1) * (2 * v1) - (P * P - 4 * Q) * ((2 * u1) * (2 * u1))
         = 4 * (Q * (v0 * v0 - (P * P - 4 * Q) * (u0 * u0))) := by
    rw [hA, hB]; ring_intZ
  -- LHS of h equals 4 * N(k+1)
  have hL : (2 * v1) * (2 * v1) - (P * P - 4 * Q) * ((2 * u1) * (2 * u1))
          = 4 * (v1 * v1 - (P * P - 4 * Q) * (u1 * u1)) := by ring_intZ
  rw [hL] at h
  exact h

theorem lucasQuadratic (P Q : Int) (n : Nat) :
    lucV P Q n * lucV P Q n - lucD P Q * (lucU P Q n * lucU P Q n)
      = 4 * powInt Q n := by
  show lucV P Q n * lucV P Q n - (P * P - 4 * Q) * (lucU P Q n * lucU P Q n)
      = 4 * powInt Q n
  induction n with
  | zero =>
    rw [lucU_zero, lucV_zero, zero_mul, mul_zeroZ]
    show (2 : Int) * 2 - 0 = 4 * 1; ring_intZ
  | succ k ih =>
    rw [powInt_succ']
    have hstep := quad_kernel P Q (lucU P Q k) (lucU P Q (k + 1))
      (lucV P Q k) (lucV P Q (k + 1)) (lucUV_cross_U P Q k) (lucUV_cross_V P Q k)
    rw [hstep, ih]; ring_intZ

end E213.ScratchLUCS.Proof
