import E213.Lib.Math.DyadicFSM.PellMatrix
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper
/-!
# Pell matrix action formula — G119 Phase 1 bridge

Connects `pellCoeff p hp k` to `(pellFSMmod p hp).run k`.

The matrix M = [[2, 1], [1, 1]] applied to v_0 = (1, 1) gives M v_0 = (3, 2).
By Cayley-Hamilton, M^k = a_k · M + b_k · I.  So:

  M^k · (1, 1) = a_k · M (1, 1) + b_k · (1, 1)
             = a_k · (3, 2) + b_k · (1, 1)
             = (3·a_k + b_k, 2·a_k + b_k)

This is the action formula.  Combined with `pellCoeff_zero_one_at_N`
(matrix-order detection), it gives the universal Pisano period theorem
restricted to the (1, 1) orbit.

This file proves the action formula by induction on k, using PURE
`add_mod_gen` + `mul_mod_*_pure` Nat arithmetic helpers.
-/

namespace E213.Lib.Math.DyadicFSM.PellMatrixAction

open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod ArithFSM2)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_self)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (add_sub_of_le sub_add_cancel add_mul mul_assoc)

/-- ★ Action formula at k=0: `pellFSMmod.run 0 = init = (1, 1)`,
    and the formula `(3·0 + 1 mod p, 2·0 + 1 mod p) = (1, 1)` matches. -/
theorem action_base (p : Nat) (hp : 1 < p) :
    ((pellFSMmod p hp).run 0).1.val
      = (3 * (pellCoeff p hp 0).1.val + (pellCoeff p hp 0).2.val) % p
    ∧ ((pellFSMmod p hp).run 0).2.val
      = (2 * (pellCoeff p hp 0).1.val + (pellCoeff p hp 0).2.val) % p := by
  refine ⟨?_, ?_⟩
  · show 1 = (3 * 0 + 1) % p
    rw [Nat.mul_zero, Nat.zero_add]
    exact (Nat.mod_eq_of_lt hp).symm
  · show 1 = (2 * 0 + 1) % p
    rw [Nat.mul_zero, Nat.zero_add]
    exact (Nat.mod_eq_of_lt hp).symm

open E213.Meta.Nat.AddMod213 (div_add_mod mod_mod)

/-- Helper: `(k * (x % p) + y % p) % p = (k * x + y) % p`.  PURE. -/
theorem mul_mod_add_mod (k x y p : Nat) :
    (k * (x % p) + y % p) % p = (k * x + y) % p := by
  rw [add_mod_gen (k * (x % p)) (y % p) p]
  -- Goal: ((k * (x % p)) % p + (y % p) % p) % p = (k * x + y) % p
  rw [mod_mod]
  -- Goal: ((k * (x % p)) % p + y % p) % p = (k * x + y) % p
  rw [← mul_mod_right_pure k x p]
  -- Goal: ((k * x) % p + y % p) % p = (k * x + y) % p
  rw [← add_mod_gen (k * x) y p]

/-- ★ Negation in `Fin p`: `a + (p - a % p) ≡ 0 (mod p)`.  PURE. -/
theorem neg_mod_sub (p a : Nat) (hp : 0 < p) :
    (a + (p - a % p)) % p = 0 := by
  have hlt : a % p < p := Nat.mod_lt a hp
  have hdivmod : p * (a / p) + a % p = a := div_add_mod a p
  have hcancel : a % p + (p - a % p) = p := add_sub_of_le (Nat.le_of_lt hlt)
  have e1 : a + (p - a % p) = p * (a / p) + p := by
    have h : a + (p - a % p) = (p * (a / p) + a % p) + (p - a % p) := by rw [hdivmod]
    rw [h, Nat.add_assoc, hcancel]
  rw [e1, add_mod_gen]
  rw [mod_self]
  rw [Nat.add_zero]
  rw [mod_mod]
  exact E213.Tactic.NatHelper.mul_mod_right p (a / p)

/-- Nat-arithmetic helper: `2 * (3a + b) + (2a + b) = 8a + 3b`.  PURE. -/
theorem nat_arith_8a_3b (a b : Nat) :
    2 * (3 * a + b) + (2 * a + b) = 8 * a + 3 * b := by
  have h1 : 2 * (3 * a + b) = 6 * a + 2 * b := by
    rw [Nat.mul_add, ← mul_assoc 2 3 a]
  rw [h1]
  have h2 : 6 * a + 2 * b + (2 * a + b) = (6 * a + 2 * a) + (2 * b + b) := by
    rw [Nat.add_assoc (6*a) (2*b) (2*a + b)]
    rw [← Nat.add_assoc (2*b) (2*a) b]
    rw [Nat.add_comm (2*b) (2*a)]
    rw [Nat.add_assoc (2*a) (2*b) b]
    rw [← Nat.add_assoc (6*a) (2*a) (2*b + b)]
  rw [h2]
  have h3 : 6 * a + 2 * a = 8 * a := by rw [← add_mul]
  have h4 : 2 * b + b = 3 * b := by
    have e : 2 * b + b = 2 * b + 1 * b := by rw [Nat.one_mul]
    rw [e, ← add_mul]
  rw [h3, h4]

/-- Arithmetic lemma A (first-component step):
    `(2 · ((3a+b) % p) + (2a+b) % p) % p = (8a + 3b) % p`.  PURE. -/
theorem action_step_lhs_1 (a b p : Nat) :
    (2 * ((3 * a + b) % p) + (2 * a + b) % p) % p
      = (8 * a + 3 * b) % p := by
  rw [mul_mod_add_mod 2 (3 * a + b) (2 * a + b) p]
  rw [nat_arith_8a_3b]

/-- Nat-arithmetic helper: `(3a + b) + (2a + b) = 5a + 2b`.  PURE. -/
theorem nat_arith_5a_2b (a b : Nat) :
    (3 * a + b) + (2 * a + b) = 5 * a + 2 * b := by
  -- Re-group: (3a + 2a) + (b + b) = 5a + 2b
  have h1 : (3 * a + b) + (2 * a + b) = (3 * a + 2 * a) + (b + b) := by
    rw [Nat.add_assoc (3*a) b (2*a + b)]
    rw [← Nat.add_assoc b (2*a) b]
    rw [Nat.add_comm b (2*a)]
    rw [Nat.add_assoc (2*a) b b]
    rw [← Nat.add_assoc (3*a) (2*a) (b + b)]
  rw [h1]
  have h2 : 3 * a + 2 * a = 5 * a := by rw [← add_mul]
  have h3 : b + b = 2 * b := by
    have e : b + b = 1 * b + 1 * b := by rw [Nat.one_mul]
    rw [e, ← add_mul]
  rw [h2, h3]

/-- Arithmetic lemma A2 (second-component step):
    `(((3a+b) % p) + (2a+b) % p) % p = (5a + 2b) % p`.  PURE. -/
theorem action_step_lhs_2 (a b p : Nat) :
    (((3 * a + b) % p) + (2 * a + b) % p) % p
      = (5 * a + 2 * b) % p := by
  rw [← add_mod_gen]
  rw [nat_arith_5a_2b]

/-- Helper: `Y % p = 0 → (X + Y) % p = X % p`.  PURE. -/
theorem add_zero_mod (X Y p : Nat) (hY : Y % p = 0) :
    (X + Y) % p = X % p := by
  rw [add_mod_gen, hY, Nat.add_zero, mod_mod]

/-- Nat-arithmetic helper: `9a + 3b + c = 8a + 3b + (a + c)`.  PURE. -/
theorem nat_arith_9a_decompose (a b c : Nat) :
    9 * a + 3 * b + c = 8 * a + 3 * b + (a + c) := by
  have h1 : (9 : Nat) * a = 8 * a + a := by
    have e : (9 : Nat) = 8 + 1 := rfl
    rw [e, add_mul, Nat.one_mul]
  rw [h1]
  rw [Nat.add_assoc (8*a) a (3*b)]
  rw [Nat.add_comm a (3*b)]
  rw [← Nat.add_assoc (8*a) (3*b) a]
  rw [Nat.add_assoc (8*a + 3*b) a c]

/-- Arithmetic lemma B1 (RHS first-component, step k+1):
    `(3 · a_{k+1} + b_{k+1}) % p = (8a + 3b) % p`.
    With `a_{k+1} = (3a+b) % p`, `b_{k+1} = (p - a%p) % p`.  PURE. -/
theorem action_step_rhs_1 (a b p : Nat) (hp : 0 < p) :
    (3 * ((3 * a + b) % p) + (p - a % p) % p) % p
      = (8 * a + 3 * b) % p := by
  -- Step 1: collapse mod p on the multiplied term + addition.
  rw [mul_mod_add_mod 3 (3 * a + b) (p - a % p) p]
  -- Goal: (3 * (3*a + b) + (p - a % p)) % p = (8*a + 3*b) % p
  -- Step 2: 3 * (3a + b) = 9a + 3b
  have h_expand : 3 * (3 * a + b) = 9 * a + 3 * b := by
    rw [Nat.mul_add, ← mul_assoc 3 3 a]
  rw [h_expand]
  -- Goal: (9*a + 3*b + (p - a%p)) % p = (8*a + 3*b) % p
  -- Step 3: regroup as (8*a + 3*b) + (a + (p - a%p))
  rw [nat_arith_9a_decompose a b (p - a % p)]
  -- Goal: (8*a + 3*b + (a + (p - a%p))) % p = (8*a + 3*b) % p
  -- Step 4: use add_zero_mod since (a + (p - a%p)) % p = 0
  exact add_zero_mod (8 * a + 3 * b) (a + (p - a % p)) p (neg_mod_sub p a hp)

/-- Nat-arithmetic helper: `6a + 2b + c = 5a + 2b + (a + c)`.  PURE. -/
theorem nat_arith_6a_decompose (a b c : Nat) :
    6 * a + 2 * b + c = 5 * a + 2 * b + (a + c) := by
  have h1 : (6 : Nat) * a = 5 * a + a := by
    have e : (6 : Nat) = 5 + 1 := rfl
    rw [e, add_mul, Nat.one_mul]
  rw [h1]
  rw [Nat.add_assoc (5*a) a (2*b)]
  rw [Nat.add_comm a (2*b)]
  rw [← Nat.add_assoc (5*a) (2*b) a]
  rw [Nat.add_assoc (5*a + 2*b) a c]

/-- Arithmetic lemma B2 (RHS second-component, step k+1):
    `(2 · a_{k+1} + b_{k+1}) % p = (5a + 2b) % p`.
    With `a_{k+1} = (3a+b) % p`, `b_{k+1} = (p - a%p) % p`.  PURE. -/
theorem action_step_rhs_2 (a b p : Nat) (hp : 0 < p) :
    (2 * ((3 * a + b) % p) + (p - a % p) % p) % p
      = (5 * a + 2 * b) % p := by
  rw [mul_mod_add_mod 2 (3 * a + b) (p - a % p) p]
  have h_expand : 2 * (3 * a + b) = 6 * a + 2 * b := by
    rw [Nat.mul_add, ← mul_assoc 2 3 a]
  rw [h_expand]
  rw [nat_arith_6a_decompose a b (p - a % p)]
  exact add_zero_mod (5 * a + 2 * b) (a + (p - a % p)) p (neg_mod_sub p a hp)

/-- Cayley-Hamilton equality (component-wise, mod p):
    LHS (pellFSMmod.step on (3a+b mod p, 2a+b mod p)) =
    RHS (formula at k+1 with new coefficients).  PURE. -/
theorem action_step_eq (a b p : Nat) (hp : 0 < p) :
    (2 * ((3 * a + b) % p) + (2 * a + b) % p) % p
      = (3 * ((3 * a + b) % p) + (p - a % p) % p) % p
    ∧ (((3 * a + b) % p) + (2 * a + b) % p) % p
      = (2 * ((3 * a + b) % p) + (p - a % p) % p) % p := by
  refine ⟨?_, ?_⟩
  · rw [action_step_lhs_1, action_step_rhs_1 a b p hp]
  · rw [action_step_lhs_2, action_step_rhs_2 a b p hp]

/-- ★ Action formula: `(pellFSMmod p hp).run k` matches the
    Cayley-Hamilton coefficients `pellCoeff p hp k` via the
    `M · (1, 1) = (3, 2)` linear action.  PURE.

    For all k, ((pellFSMmod.run k).1.val, (pellFSMmod.run k).2.val) =
    ((3·a_k + b_k) % p, (2·a_k + b_k) % p)
    where `(a_k, b_k) = pellCoeff p hp k`. -/
theorem action_general (p : Nat) (hp : 1 < p) :
    ∀ k, ((pellFSMmod p hp).run k).1.val
          = (3 * (pellCoeff p hp k).1.val + (pellCoeff p hp k).2.val) % p
        ∧ ((pellFSMmod p hp).run k).2.val
          = (2 * (pellCoeff p hp k).1.val + (pellCoeff p hp k).2.val) % p
  | 0 => action_base p hp
  | k+1 => by
    obtain ⟨ih1, ih2⟩ := action_general p hp k
    -- (pellFSMmod.run (k+1)).1.val = (2 * (run k).1.val + (run k).2.val) % p
    -- = (2 * ((3a+b) % p) + (2a+b) % p) % p [by ih]
    -- = (3 * ((3a+b) % p) + (p - a%p) % p) % p [by action_step_eq.1]
    -- = (3 * a_{k+1} + b_{k+1}) % p
    refine ⟨?_, ?_⟩
    · show (2 * ((pellFSMmod p hp).run k).1.val
              + ((pellFSMmod p hp).run k).2.val) % p
            = (3 * (pellCoeff p hp (k+1)).1.val
              + (pellCoeff p hp (k+1)).2.val) % p
      rw [ih1, ih2]
      exact (action_step_eq (pellCoeff p hp k).1.val (pellCoeff p hp k).2.val
                            p (Nat.lt_of_succ_lt hp)).1
    · show (((pellFSMmod p hp).run k).1.val + ((pellFSMmod p hp).run k).2.val) % p
            = (2 * (pellCoeff p hp (k+1)).1.val
              + (pellCoeff p hp (k+1)).2.val) % p
      rw [ih1, ih2]
      exact (action_step_eq (pellCoeff p hp k).1.val (pellCoeff p hp k).2.val
                            p (Nat.lt_of_succ_lt hp)).2

open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeffFSM pellCoeffFSM_run_eq_pellCoeff)
open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2.run_period_of_base)

/-- ★ BRIDGE THEOREM: if `pellCoeff` reaches (0, 1) at step N (i.e., the
    matrix M = [[2,1],[1,1]] has order dividing N in `GL_2(𝔽_p)`),
    then the `pellFSMmod` FSM has period N at the (1, 1) initial state.

    PURE.  Connects the matrix-order detection (`pellCoeff p hp N = (0, 1)`)
    to the FSM-period statement (`run (k+N) = run k`). -/
theorem pellCoeff_period_implies_pellFSMmod_period (p : Nat) (hp : 1 < p) (N : Nat)
    (hN : pellCoeff p hp N = (⟨0, Nat.lt_of_succ_lt hp⟩, ⟨1, hp⟩)) :
    ∀ k, (pellFSMmod p hp).run (k + N) = (pellFSMmod p hp).run k := by
  -- Step 1: pellCoeffFSM has period N (run_period_of_base).
  have h_init_eq : (pellCoeffFSM p hp).run N = (pellCoeffFSM p hp).init := by
    rw [pellCoeffFSM_run_eq_pellCoeff]
    exact hN
  have h_period :
      ∀ k, (pellCoeffFSM p hp).run (k + N) = (pellCoeffFSM p hp).run k :=
    ArithFSM2.run_period_of_base _ h_init_eq
  -- Step 2: pellCoeff (k+N) = pellCoeff k via pellCoeffFSM_run_eq.
  have h_coeff_period : ∀ k, pellCoeff p hp (k + N) = pellCoeff p hp k := fun k => by
    rw [← pellCoeffFSM_run_eq_pellCoeff, ← pellCoeffFSM_run_eq_pellCoeff]
    exact h_period k
  -- Step 3: action formula at (k+N) and k gives equal values.
  intro k
  apply Prod.ext <;> apply Fin.eq_of_val_eq
  · obtain ⟨h1, _⟩ := action_general p hp (k + N)
    obtain ⟨h1', _⟩ := action_general p hp k
    rw [h1, h1', h_coeff_period]
  · obtain ⟨_, h2⟩ := action_general p hp (k + N)
    obtain ⟨_, h2'⟩ := action_general p hp k
    rw [h2, h2', h_coeff_period]

/-- ★ BRIDGE THEOREM (bits version): if `pellCoeff` reaches (0, 1) at
    step N, the FSM has bit-period N.  Corollary of run-period via
    `ArithFSM2.bits_period_of_run_period`. -/
theorem pellCoeff_period_implies_pellFSMmod_bits_period
    (p : Nat) (hp : 1 < p) (N : Nat)
    (hN : pellCoeff p hp N = (⟨0, Nat.lt_of_succ_lt hp⟩, ⟨1, hp⟩)) :
    ∀ k, (pellFSMmod p hp).bits (k + N) = (pellFSMmod p hp).bits k :=
  E213.Lib.Math.DyadicFSM.ArithFSM.ArithFSM2.bits_period_of_run_period
    (pellFSMmod p hp)
    (pellCoeff_period_implies_pellFSMmod_period p hp N hN)

end E213.Lib.Math.DyadicFSM.PellMatrixAction
