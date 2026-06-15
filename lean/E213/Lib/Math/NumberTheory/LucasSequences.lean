import E213.Meta.Int213.PolyIntM
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core
import E213.Meta.Int213.Order

/-!
# Generalized Lucas sequences `U_n(P,Q)`, `V_n(P,Q)` over `Int` (∅-axiom)
-/

namespace E213.Lib.Math.NumberTheory.LucasSequences

open E213.Meta.Int213.PolyIntM (powInt powInt_add mul_zeroZ)
open E213.Meta.Int213
  (mul_neg mul_one neg_mul mul_assoc mul_comm mul_left_comm mul_sub sub_mul
   add_mul mul_add zero_mul zero_add int_eq_zero_of_mul_left)
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
  -- double; on each side expose the literal `2 * v1` so `hB` rewrites.
  have key : 2 * (2 * (P * u1 - Q * u0)) = 2 * (P * u1 + v1) := by
    have rhs : 2 * (P * u1 + v1) = 2 * (P * u1) + (2 * v1) := by ring_intZ
    rw [rhs, hB]
    have hv0 : v0 = 2 * u1 - P * u0 := by rw [hA]; ring_intZ
    rw [hv0]; ring_intZ
  exact mulCancelL (show (2 : Int) ≠ 0 by decide) key

theorem cross_V_kernel (P Q u0 u1 v0 v1 : Int)
    (hA : 2 * u1 = P * u0 + v0) (hB : 2 * v1 = (P * P - 4 * Q) * u0 + P * v0) :
    2 * (P * v1 - Q * v0) = (P * P - 4 * Q) * u1 + P * v1 := by
  have key : 2 * (2 * (P * v1 - Q * v0)) = 2 * ((P * P - 4 * Q) * u1 + P * v1) := by
    have lhs : 2 * (2 * (P * v1 - Q * v0))
             = P * (2 * v1) + P * (2 * v1) - 4 * (Q * v0) := by ring_intZ
    have rhs : 2 * ((P * P - 4 * Q) * u1 + P * v1)
             = 2 * ((P * P - 4 * Q) * u1) + P * (2 * v1) := by ring_intZ
    rw [lhs, rhs, hB]
    have hv0 : v0 = 2 * u1 - P * u0 := by rw [hA]; ring_intZ
    rw [hv0]; ring_intZ
  exact mulCancelL (show (2 : Int) ≠ 0 by decide) key

theorem lucUV_cross (P Q : Int) (n : Nat) :
    2 * lucU P Q (n + 1) = P * lucU P Q n + lucV P Q n
    ∧ 2 * lucV P Q (n + 1) = (P * P - 4 * Q) * lucU P Q n + P * lucV P Q n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [lucU_one, lucU_zero, lucV_zero, mul_zeroZ, zero_add]
      show (2 : Int) * 1 = 2; ring_intZ
    · rw [lucV_one, lucU_zero, lucV_zero, mul_zeroZ, zero_add]
      show (2 : Int) * P = P * 2; ring_intZ
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

/-- `4 · Q^n = V n² − D · U n²` (flipped quadratic relation, in the `D = P²−4Q`
    expanded form used by the doubling kernels). -/
theorem quadFlip (P Q : Int) (n : Nat) :
    4 * powInt Q n
      = lucV P Q n * lucV P Q n
        - (P * P - 4 * Q) * (lucU P Q n * lucU P Q n) := by
  have h := lucasQuadratic P Q n
  show 4 * powInt Q n
      = lucV P Q n * lucV P Q n - (P * P - 4 * Q) * (lucU P Q n * lucU P Q n)
  rw [show lucD P Q = P * P - 4 * Q from rfl] at h
  exact h.symm

/-! ## §5 — doubling identities

Joint invariant carried through `n → n+1` (i.e. `2n → 2n+2`):
  A : `U(2n)   = U n · V n`
  B : `U(2n+1) = U(n+1) · V n − Qⁿ`
  C : `V(2n)   = V n · V n − 2 Qⁿ`
  E : `V(2n+1) = V(n+1) · V n − P Qⁿ`
Each step kernel is a polynomial identity in the cross relations and the
quadratic relation (`4 Qⁿ = V n² − D U n²`), cancelling the factor `4`. -/

/-- A-step: `U(2n+2) = U(n+1) V(n+1)`. -/
theorem A_kernel (P Q un un1 vn vn1 q : Int)
    (hs : 2 * un1 = P * un + vn) (ht : 2 * vn1 = (P*P-4*Q) * un + P * vn)
    (hq : 4 * q = vn*vn - (P*P-4*Q)*(un*un)) :
    P * (un1 * vn - q) - Q * (un * vn) = un1 * vn1 := by
  apply mulCancelL (show (4:Int) ≠ 0 by decide)
  have l : 4 * (P * (un1 * vn - q) - Q * (un * vn))
         = P * ((2*un1) * (2*vn) - (4*q)) - Q * ((2*un) * (2*vn)) := by ring_intZ
  have r : 4 * (un1 * vn1) = (2*un1) * (2*vn1) := by ring_intZ
  rw [l, r, hs, ht, hq]; ring_intZ

/-- B-step: `U(2n+3) = U(n+2) V(n+1) − Qⁿ⁺¹`. -/
theorem B_kernel (P Q un un1 vn vn1 q : Int)
    (hs : 2 * un1 = P * un + vn) (ht : 2 * vn1 = (P*P-4*Q) * un + P * vn)
    (hq : 4 * q = vn*vn - (P*P-4*Q)*(un*un)) :
    P * (un1*vn1) - Q * (un1*vn - q) = (P*un1 - Q*un)*vn1 - q*Q := by
  apply mulCancelL (show (4:Int) ≠ 0 by decide)
  have l : 4*(P * (un1*vn1) - Q * (un1*vn - q))
         = P*((2*un1)*(2*vn1)) - Q*(2*un1*(2*vn) - (4*q)) := by ring_intZ
  have r : 4*((P*un1 - Q*un)*vn1 - q*Q)
         = (P*(2*un1) - Q*(2*un))*(2*vn1) - (4*q)*Q := by ring_intZ
  rw [l, r, hs, ht, hq]; ring_intZ

/-- C-step: `V(2n+2) = V(n+1)² − 2 Qⁿ⁺¹`. -/
theorem C_kernel (P Q un un1 vn vn1 q : Int)
    (ht : 2 * vn1 = (P*P-4*Q) * un + P * vn)
    (hq : 4 * q = vn*vn - (P*P-4*Q)*(un*un)) :
    P * (vn1*vn - P*q) - Q * (vn*vn - 2*q) = vn1*vn1 - 2*(q*Q) := by
  apply mulCancelL (show (4:Int) ≠ 0 by decide)
  have l : 4*(P * (vn1*vn - P*q) - Q * (vn*vn - 2*q))
         = P*((2*vn1)*(2*vn) - P*(4*q)) - Q*((2*vn)*(2*vn) - 2*(4*q)) := by ring_intZ
  have r : 4*(vn1*vn1 - 2*(q*Q)) = (2*vn1)*(2*vn1) - 2*((4*q)*Q) := by ring_intZ
  rw [l, r, ht, hq]; ring_intZ

/-- E-step: `V(2n+3) = V(n+2) V(n+1) − P Qⁿ⁺¹`. -/
theorem E_kernel (P Q un _un1 vn vn1 q : Int)
    (ht : 2 * vn1 = (P*P-4*Q) * un + P * vn) :
    P * (vn1*vn1 - 2*(q*Q)) - Q * (vn1*vn - P*q) = (P*vn1 - Q*vn)*vn1 - P*(q*Q) := by
  apply mulCancelL (show (4:Int) ≠ 0 by decide)
  have l : 4*(P * (vn1*vn1 - 2*(q*Q)) - Q * (vn1*vn - P*q))
         = P*((2*vn1)*(2*vn1) - 2*((4*q)*Q)) - Q*((2*vn1)*(2*vn) - P*(4*q)) := by ring_intZ
  have r : 4*((P*vn1 - Q*vn)*vn1 - P*(q*Q))
         = (P*(2*vn1) - Q*(2*vn))*(2*vn1) - P*((4*q)*Q) := by ring_intZ
  rw [l, r, ht]; ring_intZ

/-- Joint doubling invariant, by induction on `n`. -/
theorem lucasDoubleAll (P Q : Int) (n : Nat) :
    lucU P Q (2 * n) = lucU P Q n * lucV P Q n
    ∧ lucU P Q (2 * n + 1) = lucU P Q (n + 1) * lucV P Q n - powInt Q n
    ∧ lucV P Q (2 * n) = lucV P Q n * lucV P Q n - 2 * powInt Q n
    ∧ lucV P Q (2 * n + 1) = lucV P Q (n + 1) * lucV P Q n - P * powInt Q n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show lucU P Q 0 = lucU P Q 0 * lucV P Q 0
      rw [lucU_zero, lucV_zero, zero_mul]
    · show lucU P Q 1 = lucU P Q 1 * lucV P Q 0 - powInt Q 0
      rw [lucU_one, lucV_zero]; show (1:Int) = 1 * 2 - 1; ring_intZ
    · show lucV P Q 0 = lucV P Q 0 * lucV P Q 0 - 2 * powInt Q 0
      rw [lucV_zero]; show (2:Int) = 2 * 2 - 2 * 1; ring_intZ
    · show lucV P Q 1 = lucV P Q 1 * lucV P Q 0 - P * powInt Q 0
      rw [lucV_one, lucV_zero]; show P = P * 2 - P * 1; ring_intZ
  | succ k ih =>
    obtain ⟨ihA, ihB, ihC, ihE⟩ := ih
    -- abbreviations
    have hs := lucUV_cross_U P Q k
    have ht := lucUV_cross_V P Q k
    have hq := quadFlip P Q k
    -- indices: 2*(k+1) = 2*k+2 = (2*k)+2 ; 2*(k+1)+1 = 2*k+3 = (2*k+1)+2  (all rfl)
    -- A' and C' first (they feed B' and E').
    have hA' : lucU P Q (2 * k + 2) = lucU P Q (k + 1) * lucV P Q (k + 1) := by
      rw [lucU_rec, ihB, ihA]
      exact A_kernel P Q (lucU P Q k) (lucU P Q (k+1)) (lucV P Q k) (lucV P Q (k+1))
        (powInt Q k) hs ht hq
    have hC' : lucV P Q (2 * k + 2)
             = lucV P Q (k + 1) * lucV P Q (k + 1) - 2 * powInt Q (k + 1) := by
      rw [lucV_rec, ihE, ihC, powInt_succ']
      exact C_kernel P Q (lucU P Q k) (lucU P Q (k+1)) (lucV P Q k) (lucV P Q (k+1))
        (powInt Q k) ht hq
    refine ⟨hA', ?_, hC', ?_⟩
    · -- B' : U(2k+3) = U(k+2) V(k+1) - Q^(k+1)
      show lucU P Q (2 * k + 1 + 2)
          = lucU P Q (k + 1 + 1) * lucV P Q (k + 1) - powInt Q (k + 1)
      rw [lucU_rec, hA', ihB, lucU_rec (n := k), powInt_succ']
      exact B_kernel P Q (lucU P Q k) (lucU P Q (k+1)) (lucV P Q k) (lucV P Q (k+1))
        (powInt Q k) hs ht hq
    · -- E' : V(2k+3) = V(k+2) V(k+1) - P Q^(k+1)
      show lucV P Q (2 * k + 1 + 2)
          = lucV P Q (k + 1 + 1) * lucV P Q (k + 1) - P * powInt Q (k + 1)
      rw [lucV_rec, hC', ihE, lucV_rec (n := k), powInt_succ']
      exact E_kernel P Q (lucU P Q k) (lucU P Q (k+1)) (lucV P Q k) (lucV P Q (k+1))
        (powInt Q k) ht

/-- ★★★ **Doubling** (first kind): `U(2n) = U n · V n`. -/
theorem lucasDouble (P Q : Int) (n : Nat) :
    lucU P Q (2 * n) = lucU P Q n * lucV P Q n := (lucasDoubleAll P Q n).1

/-- ★★ **Doubling** (second kind): `V(2n) = V n · V n − 2 · Q^n`. -/
theorem lucasVDouble (P Q : Int) (n : Nat) :
    lucV P Q (2 * n) = lucV P Q n * lucV P Q n - 2 * powInt Q n :=
  (lucasDoubleAll P Q n).2.2.1

/-! ## §6 — concrete specializations (closed-term `decide`, axiom-clean) -/

/-- `P = 1, Q = −1` ⇒ `U` is the **Fibonacci** sequence `0,1,1,2,3,5,8,13`. -/
theorem fib_table :
    lucU 1 (-1) 0 = 0 ∧ lucU 1 (-1) 1 = 1 ∧ lucU 1 (-1) 2 = 1
    ∧ lucU 1 (-1) 3 = 2 ∧ lucU 1 (-1) 4 = 3 ∧ lucU 1 (-1) 5 = 5
    ∧ lucU 1 (-1) 6 = 8 ∧ lucU 1 (-1) 7 = 13 := by decide

/-- `P = 1, Q = −1` ⇒ `V` is the **Lucas** sequence `2,1,3,4,7,11,18`. -/
theorem lucasL_table :
    lucV 1 (-1) 0 = 2 ∧ lucV 1 (-1) 1 = 1 ∧ lucV 1 (-1) 2 = 3
    ∧ lucV 1 (-1) 3 = 4 ∧ lucV 1 (-1) 4 = 7 ∧ lucV 1 (-1) 5 = 11
    ∧ lucV 1 (-1) 6 = 18 := by decide

/-- `P = 2, Q = −1` ⇒ `U` is the **Pell** sequence `0,1,2,5,12,29,70`. -/
theorem pell_table :
    lucU 2 (-1) 0 = 0 ∧ lucU 2 (-1) 1 = 1 ∧ lucU 2 (-1) 2 = 2
    ∧ lucU 2 (-1) 3 = 5 ∧ lucU 2 (-1) 4 = 12 ∧ lucU 2 (-1) 5 = 29
    ∧ lucU 2 (-1) 6 = 70 := by decide

/-- `P = 2, Q = −1` ⇒ `V` is the **Pell–Lucas (companion Pell)** sequence
    `2,2,6,14,34,82`. -/
theorem pellV_table :
    lucV 2 (-1) 0 = 2 ∧ lucV 2 (-1) 1 = 2 ∧ lucV 2 (-1) 2 = 6
    ∧ lucV 2 (-1) 3 = 14 ∧ lucV 2 (-1) 4 = 34 ∧ lucV 2 (-1) 5 = 82 := by decide

/-- Quadratic relation smoke (Fibonacci/Lucas, `n = 6`, `D = 5`):
    `V₆² − 5·U₆² = 18² − 5·8² = 324 − 320 = 4 = 4·(−1)⁶`. -/
theorem fib_quad_smoke :
    lucV 1 (-1) 6 * lucV 1 (-1) 6 - lucD 1 (-1) * (lucU 1 (-1) 6 * lucU 1 (-1) 6)
      = 4 * powInt (-1) 6 := by decide

/-- Pell quadratic relation smoke (`n = 5`, `D = 8`):
    `V₅² − 8·U₅² = 82² − 8·29² = 6724 − 6728 = −4 = 4·(−1)⁵`. -/
theorem pell_quad_smoke :
    lucV 2 (-1) 5 * lucV 2 (-1) 5 - lucD 2 (-1) * (lucU 2 (-1) 5 * lucU 2 (-1) 5)
      = 4 * powInt (-1) 5 := by decide

/-- Doubling smoke (Fibonacci, `n = 3`): `U₆ = U₃ · V₃ = 2 · 4 = 8`. -/
theorem fib_double_smoke :
    lucU 1 (-1) (2 * 3) = lucU 1 (-1) 3 * lucV 1 (-1) 3 := by decide

end E213.Lib.Math.NumberTheory.LucasSequences
