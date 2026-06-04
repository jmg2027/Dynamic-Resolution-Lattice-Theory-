import E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper
/-!
# Pell matrix step invertibility — G119 Phase 2

The pellCoeff step `(a, b) → (3a + b mod p, -a mod p)` is invertible.
The inverse `stepInv (a, b) = (-b mod p, (a + 3b) mod p)` satisfies

  `stepInv (step v) = v`     for all `v : Fin p × Fin p`,  any `p > 1`.

This is the structural ingredient for pigeonhole-existence of a Pisano
period: iterations of `step` are injective on the size-`p²` state
space, so `pellCoeff p hp` must return to `(0, 1)` in `≤ p²` steps for
every prime `p`.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixInverse

open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix (pellCoeff stepInv pellCoeffFSM)
open E213.Meta.Nat.AddMod213 (mod_self mod_mod add_mod_gen)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Tactic.NatHelper (mul_sub sub_sub_self add_mul mul_assoc)

/-- Double-negation mod p:  `(p - (p - x) % p) % p = x` for `x < p`, `1 < p`.
    PURE.  Case split on `x = 0` vs `x = n+1`. -/
theorem neg_neg_mod (p x : Nat) (hp : 1 < p) (hx : x < p) :
    (p - (p - x) % p) % p = x := by
  match x, hx with
  | 0, _ =>
    show (p - (p - 0) % p) % p = 0
    rw [Nat.sub_zero]
    rw [mod_self]
    rw [Nat.sub_zero]
    exact mod_self p
  | n+1, hn1 =>
    have hpn : 0 < n+1 := Nat.zero_lt_succ n
    have hpx : p - (n+1) < p :=
      Nat.sub_lt (Nat.lt_of_succ_lt hp) hpn
    rw [Nat.mod_eq_of_lt hpx]
    rw [sub_sub_self (Nat.le_of_lt hn1)]
    exact Nat.mod_eq_of_lt hn1

/-- Helper: `3 * (p - a) = 3 * p - 3 * a` (truncated subtraction in Nat).
    PURE.  Direct invocation of `mul_sub`. -/
theorem three_mul_sub (p a : Nat) : 3 * (p - a) = 3 * p - 3 * a :=
  mul_sub 3 p a

open E213.Tactic.NatHelper (add_sub_of_le)

/-- Helper: `3a + b + (3p - 3a) = b + 3 * p` in Nat, given `a ≤ p`.  PURE. -/
theorem b_plus_three_p (p a b : Nat) (h : a ≤ p) :
    3 * a + b + (3 * p - 3 * a) = b + 3 * p := by
  have h3a : 3 * a ≤ 3 * p := Nat.mul_le_mul_left 3 h
  -- Goal: 3 * a + b + (3 * p - 3 * a) = b + 3 * p
  rw [Nat.add_assoc]
  rw [Nat.add_comm b (3 * p - 3 * a)]
  rw [← Nat.add_assoc]
  -- Goal: 3 * a + (3 * p - 3 * a) + b = b + 3 * p
  rw [add_sub_of_le h3a]
  -- Goal: 3 * p + b = b + 3 * p
  exact Nat.add_comm (3 * p) b

/-- The b-component of `stepInv ∘ step`: returns `b`.
    `((3a + b) % p + 3 * ((p - a) % p)) % p = b`, given `a < p`, `b < p`. -/
theorem step_b_cancel (p a b : Nat) (ha : a < p) (hb : b < p) :
    ((3 * a + b) % p + 3 * ((p - a) % p)) % p = b := by
  -- Step 1: combine the outer add via add_mod_gen.
  rw [add_mod_gen ((3 * a + b) % p) (3 * ((p - a) % p)) p]
  rw [mod_mod]
  -- Goal: ((3 * a + b) % p + 3 * ((p - a) % p) % p) % p = b
  -- Step 2: push the inner mod off the (p - a) factor.
  rw [← mul_mod_right_pure 3 (p - a) p]
  -- Goal: ((3 * a + b) % p + 3 * (p - a) % p) % p = b
  -- Step 3: combine the two %p's back via add_mod_gen backwards.
  rw [← add_mod_gen (3 * a + b) (3 * (p - a)) p]
  -- Goal: (3 * a + b + 3 * (p - a)) % p = b
  rw [three_mul_sub]
  -- Goal: (3 * a + b + (3 * p - 3 * a)) % p = b
  rw [b_plus_three_p p a b (Nat.le_of_lt ha)]
  -- Goal: (b + 3 * p) % p = b
  rw [E213.Tactic.NatHelper.add_mul_mod_self_pure b p 3]
  exact Nat.mod_eq_of_lt hb

open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix (pellCoeffFSM_run_eq_pellCoeff)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)

/-- The `pellCoeffFSM`'s `step` agrees with the `pellCoeff` recurrence:
    applying it to `pellCoeff k` gives `pellCoeff (k+1)`.  Definitional. -/
theorem pellCoeffFSM_step_pellCoeff (p : Nat) (hp : 1 < p) (k : Nat) :
    (pellCoeffFSM p hp).step (pellCoeff p hp k) = pellCoeff p hp (k + 1) := rfl

/-- Universal `stepInv ∘ step = id` on `Fin p × Fin p`.  PURE. -/
theorem stepInv_step (p : Nat) (hp : 1 < p) (v : Fin p × Fin p) :
    stepInv p hp ((pellCoeffFSM p hp).step v) = v := by
  obtain ⟨a, b⟩ := v
  apply Prod.ext
  · -- First component: (Fin p equality).
    apply Fin.ext
    show (p - ((p - a.val % p) % p) % p) % p = a.val
    rw [Nat.mod_eq_of_lt a.isLt]
    rw [mod_mod]
    exact neg_neg_mod p a.val hp a.isLt
  · -- Second component: (Fin p equality).
    apply Fin.ext
    show ((3 * a.val + b.val) % p + 3 * ((p - a.val % p) % p)) % p = b.val
    rw [Nat.mod_eq_of_lt a.isLt]
    exact step_b_cancel p a.val b.val a.isLt b.isLt

/-- `stepInv` undoes one `pellCoeff` step: stepInv (pellCoeff (k+1)) = pellCoeff k. -/
theorem stepInv_pellCoeff_succ (p : Nat) (hp : 1 < p) (k : Nat) :
    stepInv p hp (pellCoeff p hp (k + 1)) = pellCoeff p hp k := by
  rw [← pellCoeffFSM_step_pellCoeff p hp k]
  exact stepInv_step p hp (pellCoeff p hp k)

/-- Translation lemma:  if `pellCoeff p hp i = pellCoeff p hp j` and `i ≤ j`,
    then `pellCoeff p hp (j - i) = pellCoeff p hp 0 = (0, 1)`.

    This is the existential Pisano period mechanism: any coincidence at index
    `(i, j)` in the pellCoeff sequence produces a period `j - i`. -/
theorem pellCoeff_translation (p : Nat) (hp : 1 < p) :
    ∀ i j, i ≤ j → pellCoeff p hp i = pellCoeff p hp j →
      pellCoeff p hp (j - i) = pellCoeff p hp 0
  | 0, j, _, h => by rw [Nat.sub_zero]; exact h.symm
  | i+1, j, hij, h => by
    -- From `i+1 ≤ j` we get `j ≥ 1`, so `j = m+1` for some `m`.
    match j, hij, h with
    | m+1, hm1, h' =>
      -- Apply stepInv to both sides of h' : pellCoeff (i+1) = pellCoeff (m+1).
      have hstep : stepInv p hp (pellCoeff p hp (i+1)) =
                   stepInv p hp (pellCoeff p hp (m+1)) := congrArg _ h'
      rw [stepInv_pellCoeff_succ p hp i,
          stepInv_pellCoeff_succ p hp m] at hstep
      -- hstep : pellCoeff i = pellCoeff m
      have him : i ≤ m := Nat.le_of_succ_le_succ hm1
      have hrec : pellCoeff p hp (m - i) = pellCoeff p hp 0 :=
        pellCoeff_translation p hp i m him hstep
      -- m + 1 - (i + 1) = m - i.
      show pellCoeff p hp (m + 1 - (i + 1)) = pellCoeff p hp 0
      rw [Nat.succ_sub_succ_eq_sub]
      exact hrec

end E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixInverse
