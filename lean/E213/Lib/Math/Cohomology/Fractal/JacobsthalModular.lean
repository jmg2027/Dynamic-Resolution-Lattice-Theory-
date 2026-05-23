import E213.Lib.Math.Cohomology.Fractal.JacobsthalCutoff
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper

/-!
# Jacobsthal-sequence modular fingerprint

Companion to `JacobsthalCutoff.lean`.  Jacobsthal's recurrence
`J_{n+2} = J_{n+1} + 2 J_n` has the structural feature that the
`2 J_n` term vanishes modulo 2, giving a particularly clean
eventually-constant readout at the smallest prime.

Closed form `J_n = (2^n − (−1)^n) / 3` also constrains the
periods at higher moduli via the order of 2 modulo `p` /
modulo `3 p`.

## Periods at small primes

| p | π_J(p) | structure                                           |
|---|--------|-----------------------------------------------------|
| 2 | 1 (eventually const) | `J_n = 1` for all `n ≥ 1` ★ parametric |
| 3 | 6      | `0, 1, 1, 0, 2, 2` ★ parametric (2-step induction)  |
| 5 | 4      | `0, 1, 1, 3` ★ parametric (2-step induction)        |

## Why mod 2 collapses to a constant

`J_{n+2} % 2 = (J_{n+1} + 2 J_n) % 2 = J_{n+1} % 2`, hence the
mod-2 sequence is constant from index 1.  Combined with `J_1 = 1`,
every `J_n` is odd for `n ≥ 1`.  This is the structural
complement to the Hunter-atom parity spectrum.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Fractal.JacobsthalModular

open E213.Lib.Math.Cohomology.Fractal.JacobsthalCutoff (Jac)
open E213.Meta.Nat.AddMod213
open E213.Meta.Nat.MulMod213 (mul_mod_right_pure)
open E213.Tactic.NatHelper (mul_mod_right mod_mod_pure)

/-! ## §1 Mod-2 eventually constant `1` from `n = 1`

The `2 J_n` term in the recurrence vanishes modulo 2, so the
mod-2 sequence inherits the parity of the previous term.
Combined with `J_1 = 1`, every `J_n` for `n ≥ 1` is odd. -/

theorem Jac_0_mod_2 : Jac 0 % 2 = 0 := by decide
theorem Jac_1_mod_2 : Jac 1 % 2 = 1 := by decide

/-- ★ **Eventually constant `1` mod 2** from `n = 1`:
    `Jac (n + 1) % 2 = 1` for every `n : Nat`.

    Proof: Nat induction on `n`.  Base `J_1 = 1`.  Step uses the
    recurrence `J_{k+2} = J_{k+1} + 2 J_k` and the fact that
    `2 J_k % 2 = 0`, reducing `J_{k+2} % 2` to `J_{k+1} % 2`. -/
theorem Jac_succ_mod_2 : ∀ n, Jac (n + 1) % 2 = 1
  | 0     => by decide
  | k + 1 => by
      have ih : Jac (k + 1) % 2 = 1 := Jac_succ_mod_2 k
      have h_rec : Jac (k + 2) = Jac (k + 1) + 2 * Jac k := rfl
      have h_split : (Jac (k + 1) + 2 * Jac k) % 2
          = ((Jac (k + 1) % 2) + (2 * Jac k) % 2) % 2 :=
        add_mod_gen (Jac (k + 1)) (2 * Jac k) 2
      have h_2_even : (2 * Jac k) % 2 = 0 := mul_mod_right 2 (Jac k)
      have h_collapse : ((Jac (k + 1) % 2) + (2 * Jac k) % 2) % 2
                     = ((Jac (k + 1) % 2) + 0) % 2 :=
        congrArg (fun x => ((Jac (k + 1) % 2) + x) % 2) h_2_even
      have h_add_zero : ((Jac (k + 1) % 2) + 0) % 2
                      = (Jac (k + 1) % 2) % 2 :=
        congrArg (· % 2) (Nat.add_zero _)
      have h_mod_mod : (Jac (k + 1) % 2) % 2 = Jac (k + 1) % 2 :=
        mod_mod_pure (Jac (k + 1)) 2
      show Jac (k + 2) % 2 = 1
      rw [h_rec, h_split, h_collapse, h_add_zero, h_mod_mod, ih]

/-! ## §2 Mod-3 period 6 — parametric

2-step induction.  Base cases at `n ∈ {0, 1}` verified by
`decide`; step uses the recurrence + `add_mod_gen` for the sum
+ `mul_mod_right_pure` for the `2 J_n` term. -/

theorem Jac_0_mod_3 : Jac 0 % 3 = 0 := by decide
theorem Jac_1_mod_3 : Jac 1 % 3 = 1 := by decide
theorem Jac_6_mod_3 : Jac 6 % 3 = 0 := by decide
theorem Jac_7_mod_3 : Jac 7 % 3 = 1 := by decide

/-- Helper: `(2 * Jac k) % 3 = (2 * (Jac k % 3)) % 3` and similar.
    Direct from `mul_mod_right_pure`. -/
private theorem two_jac_mod (k m : Nat) :
    (2 * Jac k) % m = (2 * (Jac k % m)) % m :=
  mul_mod_right_pure 2 (Jac k) m

/-- ★ **Period 6 mod 3 for Jacobsthal**:
    `Jac (n + 6) % 3 = Jac n % 3` for every `n : Nat`. -/
theorem Jac_mod_3_period_6 : ∀ n, Jac (n + 6) % 3 = Jac n % 3
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Jac (n + 8) = Jac (n + 7) + 2 * Jac (n + 6) := by
        show Jac ((n + 6) + 2) = Jac (n + 7) + 2 * Jac (n + 6)
        rfl
      have h_rhs : Jac (n + 2) = Jac (n + 1) + 2 * Jac n := rfl
      have ih0 : Jac (n + 6) % 3 = Jac n % 3 := Jac_mod_3_period_6 n
      have ih1 : Jac ((n + 1) + 6) % 3 = Jac (n + 1) % 3 :=
        Jac_mod_3_period_6 (n + 1)
      have ih1' : Jac (n + 7) % 3 = Jac (n + 1) % 3 := ih1
      have h_lhs_mod : Jac (n + 8) % 3
          = ((Jac (n + 7) % 3) + (2 * Jac (n + 6)) % 3) % 3 := by
        rw [h_lhs]; exact add_mod_gen (Jac (n + 7)) (2 * Jac (n + 6)) 3
      have h_rhs_mod : Jac (n + 2) % 3
          = ((Jac (n + 1) % 3) + (2 * Jac n) % 3) % 3 := by
        rw [h_rhs]; exact add_mod_gen (Jac (n + 1)) (2 * Jac n) 3
      have h_2_l : (2 * Jac (n + 6)) % 3 = (2 * (Jac (n + 6) % 3)) % 3 :=
        two_jac_mod (n + 6) 3
      have h_2_r : (2 * Jac n) % 3 = (2 * (Jac n % 3)) % 3 :=
        two_jac_mod n 3
      have h_2_eq : (2 * (Jac (n + 6) % 3)) % 3 = (2 * (Jac n % 3)) % 3 :=
        congrArg (fun x => (2 * x) % 3) ih0
      have h_2_lr : (2 * Jac (n + 6)) % 3 = (2 * Jac n) % 3 :=
        (h_2_l.trans h_2_eq).trans h_2_r.symm
      have h_swap : ((Jac (n + 7) % 3) + (2 * Jac (n + 6)) % 3) % 3
                  = ((Jac (n + 1) % 3) + (2 * Jac n) % 3) % 3 := by
        rw [ih1', h_2_lr]
      show Jac ((n + 2) + 6) % 3 = Jac (n + 2) % 3
      have h_indices : (n + 2) + 6 = n + 8 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3 Mod-5 period 4 — parametric

Same template as mod-3 period 6, smaller period due to the
multiplier `2` interacting with modulus `5` (mul order of `2`
mod `5` is `4`). -/

theorem Jac_0_mod_5 : Jac 0 % 5 = 0 := by decide
theorem Jac_1_mod_5 : Jac 1 % 5 = 1 := by decide
theorem Jac_4_mod_5 : Jac 4 % 5 = 0 := by decide
theorem Jac_5_mod_5 : Jac 5 % 5 = 1 := by decide

/-- ★ **Period 4 mod 5 for Jacobsthal**:
    `Jac (n + 4) % 5 = Jac n % 5` for every `n : Nat`.

    Shortest period in the Jacobsthal modular fingerprint among
    the small primes; reflects the mul-order of `2` mod `5` being
    exactly `4`. -/
theorem Jac_mod_5_period_4 : ∀ n, Jac (n + 4) % 5 = Jac n % 5
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Jac (n + 6) = Jac (n + 5) + 2 * Jac (n + 4) := by
        show Jac ((n + 4) + 2) = Jac (n + 5) + 2 * Jac (n + 4)
        rfl
      have h_rhs : Jac (n + 2) = Jac (n + 1) + 2 * Jac n := rfl
      have ih0 : Jac (n + 4) % 5 = Jac n % 5 := Jac_mod_5_period_4 n
      have ih1 : Jac ((n + 1) + 4) % 5 = Jac (n + 1) % 5 :=
        Jac_mod_5_period_4 (n + 1)
      have ih1' : Jac (n + 5) % 5 = Jac (n + 1) % 5 := ih1
      have h_lhs_mod : Jac (n + 6) % 5
          = ((Jac (n + 5) % 5) + (2 * Jac (n + 4)) % 5) % 5 := by
        rw [h_lhs]; exact add_mod_gen (Jac (n + 5)) (2 * Jac (n + 4)) 5
      have h_rhs_mod : Jac (n + 2) % 5
          = ((Jac (n + 1) % 5) + (2 * Jac n) % 5) % 5 := by
        rw [h_rhs]; exact add_mod_gen (Jac (n + 1)) (2 * Jac n) 5
      have h_2_l : (2 * Jac (n + 4)) % 5 = (2 * (Jac (n + 4) % 5)) % 5 :=
        two_jac_mod (n + 4) 5
      have h_2_r : (2 * Jac n) % 5 = (2 * (Jac n % 5)) % 5 :=
        two_jac_mod n 5
      have h_2_eq : (2 * (Jac (n + 4) % 5)) % 5 = (2 * (Jac n % 5)) % 5 :=
        congrArg (fun x => (2 * x) % 5) ih0
      have h_2_lr : (2 * Jac (n + 4)) % 5 = (2 * Jac n) % 5 :=
        (h_2_l.trans h_2_eq).trans h_2_r.symm
      have h_swap : ((Jac (n + 5) % 5) + (2 * Jac (n + 4)) % 5) % 5
                  = ((Jac (n + 1) % 5) + (2 * Jac n) % 5) % 5 := by
        rw [ih1', h_2_lr]
      show Jac ((n + 2) + 4) % 5 = Jac (n + 2) % 5
      have h_indices : (n + 2) + 4 = n + 6 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3' Mod-7 period 6 — parametric

Shortest Jacobsthal mod-7 period among small primes.  Same
2-step induction template; `mul_mod_right_pure` handles `2 J_n`. -/

theorem Jac_0_mod_7 : Jac 0 % 7 = 0 := by decide
theorem Jac_1_mod_7 : Jac 1 % 7 = 1 := by decide
theorem Jac_6_mod_7 : Jac 6 % 7 = 0 := by decide
theorem Jac_7_mod_7 : Jac 7 % 7 = 1 := by decide

/-- ★ **Period 6 mod 7 for Jacobsthal**:
    `Jac (n + 6) % 7 = Jac n % 7` for every `n : Nat`. -/
theorem Jac_mod_7_period_6 : ∀ n, Jac (n + 6) % 7 = Jac n % 7
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Jac (n + 8) = Jac (n + 7) + 2 * Jac (n + 6) := by
        show Jac ((n + 6) + 2) = Jac (n + 7) + 2 * Jac (n + 6)
        rfl
      have h_rhs : Jac (n + 2) = Jac (n + 1) + 2 * Jac n := rfl
      have ih0 : Jac (n + 6) % 7 = Jac n % 7 := Jac_mod_7_period_6 n
      have ih1 : Jac ((n + 1) + 6) % 7 = Jac (n + 1) % 7 :=
        Jac_mod_7_period_6 (n + 1)
      have ih1' : Jac (n + 7) % 7 = Jac (n + 1) % 7 := ih1
      have h_lhs_mod : Jac (n + 8) % 7
          = ((Jac (n + 7) % 7) + (2 * Jac (n + 6)) % 7) % 7 := by
        rw [h_lhs]; exact add_mod_gen (Jac (n + 7)) (2 * Jac (n + 6)) 7
      have h_rhs_mod : Jac (n + 2) % 7
          = ((Jac (n + 1) % 7) + (2 * Jac n) % 7) % 7 := by
        rw [h_rhs]; exact add_mod_gen (Jac (n + 1)) (2 * Jac n) 7
      have h_2_l : (2 * Jac (n + 6)) % 7 = (2 * (Jac (n + 6) % 7)) % 7 :=
        two_jac_mod (n + 6) 7
      have h_2_r : (2 * Jac n) % 7 = (2 * (Jac n % 7)) % 7 :=
        two_jac_mod n 7
      have h_2_eq : (2 * (Jac (n + 6) % 7)) % 7 = (2 * (Jac n % 7)) % 7 :=
        congrArg (fun x => (2 * x) % 7) ih0
      have h_2_lr : (2 * Jac (n + 6)) % 7 = (2 * Jac n) % 7 :=
        (h_2_l.trans h_2_eq).trans h_2_r.symm
      have h_swap : ((Jac (n + 7) % 7) + (2 * Jac (n + 6)) % 7) % 7
                  = ((Jac (n + 1) % 7) + (2 * Jac n) % 7) % 7 := by
        rw [ih1', h_2_lr]
      show Jac ((n + 2) + 6) % 7 = Jac (n + 2) % 7
      have h_indices : (n + 2) + 6 = n + 8 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §4 Capstone -/

/-- ★★★ **Jacobsthal modular-fingerprint capstone**.  Four
    parametric closures: eventually-constant `1` mod 2 from
    `n = 1`, period 6 mod 3, period 4 mod 5, period 6 mod 7. -/
theorem capstone :
    -- Mod-2 eventually constant 1 from n = 1
    (∀ n, Jac (n + 1) % 2 = 1)
    -- Parametric period 6 mod 3
    ∧ (∀ n, Jac (n + 6) % 3 = Jac n % 3)
    -- Parametric period 4 mod 5
    ∧ (∀ n, Jac (n + 4) % 5 = Jac n % 5)
    -- Parametric period 6 mod 7
    ∧ (∀ n, Jac (n + 6) % 7 = Jac n % 7) :=
  ⟨Jac_succ_mod_2, Jac_mod_3_period_6, Jac_mod_5_period_4,
   Jac_mod_7_period_6⟩

end E213.Lib.Math.Cohomology.Fractal.JacobsthalModular
