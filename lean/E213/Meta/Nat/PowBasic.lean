import E213.Meta.Nat.PureNat
import E213.Meta.Nat.NatRing213
import E213.Meta.Tactic.NatHelper

/-!
# PowBasic — pure power toolkit over an arbitrary base

Axiom-free `Nat.pow` comparison lemmas for an arbitrary base.  The Lean-core
counterparts (`Nat.pow_le_pow_left`, `Nat.one_le_pow`, `Nat.pow_mul`, …) pull
`propext`; `Meta/Tactic/Pow213` covers the base-2 specializations.

All zero-axiom.
-/

namespace E213.Meta.Nat.PowBasic

open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_left)
open E213.Tactic.NatHelper (lt_of_le_lt)

theorem powBase_le {m M : Nat} (h : m ≤ M) : ∀ q, m^q ≤ M^q
  | 0 => Nat.le_refl 1
  | q+1 => by
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul (powBase_le h q) h

theorem one_pow_pure : ∀ q, (1:Nat)^q = 1
  | 0 => rfl
  | q+1 => by rw [Nat.pow_succ, one_pow_pure q]

theorem one_le_pow {M : Nat} (h : 1 ≤ M) (q : Nat) : 1 ≤ M^q := by
  have h1 := powBase_le h q
  rwa [one_pow_pure q] at h1

theorem powBase_lt {m M : Nat} (h : m < M) {q : Nat} (hq : 1 ≤ q) : m^q < M^q := by
  match q, hq with
  | t+1, _ =>
    rw [Nat.pow_succ, Nat.pow_succ]
    have h1 : m^t * m ≤ M^t * m := Nat.mul_le_mul_right m (powBase_le (Nat.le_of_lt h) t)
    have hMt : 0 < M^t := one_le_pow (Nat.lt_of_le_of_lt (Nat.zero_le m) h) t
    exact lt_of_le_lt h1 (nat_mul_lt_mul_left hMt h)

theorem self_le_pow (x : Nat) {q : Nat} (hq : 1 ≤ q) : x ≤ x^q := by
  match q, hq with
  | t+1, _ =>
    match x with
    | 0 => exact Nat.zero_le _
    | y+1 =>
      rw [Nat.pow_succ]
      have h1 : 1 * (y+1) ≤ (y+1)^t * (y+1) :=
        Nat.mul_le_mul_right (y+1) (one_le_pow (Nat.succ_le_succ (Nat.zero_le y)) t)
      rw [Nat.one_mul] at h1
      exact h1

theorem pow_mul_pure (x a : Nat) : ∀ b, x^(a*b) = (x^a)^b
  | 0 => by rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | b+1 => by
      rw [Nat.mul_succ, pow_add x (a*b) a, pow_mul_pure x a b, Nat.pow_succ]

end E213.Meta.Nat.PowBasic
