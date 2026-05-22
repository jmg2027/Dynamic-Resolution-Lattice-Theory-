import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
import E213.Lib.Math.ModArith.ModBezoutInvariant
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Hensel scaffold

Foundations for Hensel lifting in `ZpSeq p`.  The classical theorem
states: given a polynomial `f` with `f(a₀) ≡ 0 (mod p)` and
`f'(a₀) ≢ 0 (mod p)`, there is a unique p-adic integer `a` lifting
`a₀ ∈ F_p` such that `f(a) = 0` in `ℤ_p`.

The primary application in DRLT context: **multiplicative inverse**.
Given `x : ZpSeq p` with `(x.digits 0).val` coprime to `p`,
construct `y : ZpSeq p` such that `Zp.mul x y` is digit-by-digit
the all-one (`ZpSeq.one`) sequence — i.e., `x · y = 1` in ℤ_p.

The base case (digit 0 of y) uses the modular-arithmetic substrate
from `E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout`.
Subsequent digits are determined by the Hensel lift / FSM
correction at each level.

This module scaffolds the type signatures.  The full constructions
land here as the campaign progresses.
-/

namespace E213.Lib.Math.Padic

/-! ## Coprimality predicate

`Zp.unit0 x` — the digit-0 of `x` is nonzero.  This is the
necessary condition for `x` to be invertible in `ℤ_p` (and
sufficient when `p` is prime).
-/

/-- The unit predicate: digit-0 nonzero. -/
def Zp.unit0 {p : Nat} (x : ZpSeq p) : Prop :=
  (x.digits 0).val ≠ 0

/-- `unit0` is decidable. -/
instance Zp.unit0_decidable {p : Nat} (x : ZpSeq p) : Decidable (Zp.unit0 x) :=
  by unfold Zp.unit0; infer_instance

/-- For `ZpSeq.one`, `unit0` holds (when `1 < p`). -/
theorem Zp.unit0_one {p : Nat} (hp : 1 < p) : Zp.unit0 (ZpSeq.one p hp) := by
  show ((ZpSeq.one p hp).digits 0).val ≠ 0
  show (if (0 : Nat) = 0 then (1 : Nat) else 0) ≠ 0
  rw [if_pos rfl]
  exact fun h => Nat.noConfusion h

/-- `ZpSeq.zero` is not a unit. -/
theorem Zp.not_unit0_zero {p : Nat} (hp : 0 < p) :
    ¬ Zp.unit0 (ZpSeq.zero p hp) := by
  show ¬ ((ZpSeq.zero p hp).digits 0).val ≠ 0
  show ¬ (0 ≠ 0)
  exact fun h => h rfl

/-! ## Digit-0 inverse via Bezout

Given `x : ZpSeq p` with `(x.digits 0).val` coprime to `p`
(`gcd = 1`), the digit-0 of `x`'s inverse is the modular Bezout
inverse: a `Fin p` satisfying `(x.digits 0).val · y₀ ≡ 1 (mod p)`.

For prime `p`, `unit0 x` (digit-0 nonzero) is enough by Fermat;
for general `p`, we need the explicit gcd-1 hypothesis.

This is the base case of Hensel lifting for the multiplicative
inverse construction.
-/

/-- The digit-0 of `x`'s inverse — the modular Bezout witness
    for `(x.digits 0).val` mod `p`. -/
def Zp.invDigit0 (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ZpDigit p :=
  let mi := E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout
              (x.digits 0).val p hp h_gcd
  ⟨mi.inv, mi.inv_lt⟩

/-- The digit-0 inverse satisfies the modular identity
    `(x.digits 0).val · invDigit0 ≡ 1 (mod p)`. -/
theorem Zp.invDigit0_eq (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ((x.digits 0).val * (Zp.invDigit0 p hp x h_gcd).val) % p = 1 % p :=
  (E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout
    (x.digits 0).val p hp h_gcd).inv_eq

/-! ## Smoke applications -/

/-- Smoke: for `x : ZpSeq 5` with digit-0 = 2, the inverse digit
    is `3` (since `2 · 3 = 6 ≡ 1 (mod 5)`). -/
example (digits_rest : Nat → ZpDigit 5)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout 2 5).1 = 1) :
    (Zp.invDigit0 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else digits_rest k⟩
      h_gcd).val = 3 := by
  show (E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout
          2 5 (by decide) h_gcd).inv = 3
  rfl

/-! ## Level-1 inverse template

The "template" inverse: digit 0 is `invDigit0`, all other digits 0.
At level 1, this template multiplied by `x` truncates to `1 % p`
— the base case of the full Hensel lift.
-/

/-- The level-1 inverse template: only digit 0 is set (to the
    Bezout inverse); all higher digits are zero. -/
def Zp.invTemplate (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) : ZpSeq p where
  digits := fun k =>
    if k = 0 then Zp.invDigit0 p hp x h_gcd else ⟨0, hp⟩

/-- Digit-0 of the template equals `invDigit0`. -/
theorem Zp.invTemplate_digit_zero (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ((Zp.invTemplate p hp x h_gcd).digits 0).val
      = (Zp.invDigit0 p hp x h_gcd).val := by
  show (if (0 : Nat) = 0 then Zp.invDigit0 p hp x h_gcd
        else (⟨0, hp⟩ : Fin p)).val
      = (Zp.invDigit0 p hp x h_gcd).val
  rw [if_pos rfl]

/-- Higher digits of the template are zero. -/
theorem Zp.invTemplate_digit_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (k : Nat) :
    ((Zp.invTemplate p hp x h_gcd).digits (k + 1)).val = 0 := by
  show (if (k + 1 : Nat) = 0 then Zp.invDigit0 p hp x h_gcd
        else (⟨0, hp⟩ : Fin p)).val = 0
  rw [if_neg (fun h => Nat.noConfusion h)]

/-- Level-1 Hensel correctness: `x · invTemplate ≡ 1 (mod p)`.
    The base case of the Hensel-lifted inverse construction. -/
theorem Zp.mul_invTemplate_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    (Zp.mul p hp x (Zp.invTemplate p hp x h_gcd)).trunc 1 = 1 % p := by
  show (0 : Nat)
        + ((Zp.mul p hp x (Zp.invTemplate p hp x h_gcd)).digits 0).val * p^0
      = 1 % p
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  show ((Zp.mul p hp x (Zp.invTemplate p hp x h_gcd)).digits 0).val = 1 % p
  show (Zp.mulRaw p x (Zp.invTemplate p hp x h_gcd) 0
          + Zp.mulCarry p x (Zp.invTemplate p hp x h_gcd) 0) % p
      = 1 % p
  -- mulCarry 0 = 0 (by def).
  show (Zp.mulRaw p x (Zp.invTemplate p hp x h_gcd) 0 + 0) % p = 1 % p
  rw [Nat.add_zero]
  -- mulRaw 0 = mulRawSum 0 1 = 0 + (x.digits 0).val * (invT.digits 0).val
  show ((0 : Nat) + (x.digits 0).val
          * ((Zp.invTemplate p hp x h_gcd).digits (0 - 0)).val) % p = 1 % p
  rw [Nat.sub_zero, Nat.zero_add]
  -- Replace (invT.digits 0).val with (invDigit0).val.
  rw [Zp.invTemplate_digit_zero p hp x h_gcd]
  -- Final: ((x.digits 0).val · (invDigit0).val) % p = 1 % p
  exact Zp.invDigit0_eq p hp x h_gcd

/-! ## Negation modulo `p`

For Hensel-lift corrections, we need `(-a) mod p` in `Nat` form:
the unique value in `[0, p)` that, added to `a mod p`, gives `0 mod p`.
-/

/-- Negation modulo `p`: `(p - a % p) % p`, the additive inverse
    of `a` in `ℤ/p`. -/
def Zp.negMod (p a : Nat) : Nat := (p - a % p) % p

/-- `negMod p a < p` when `0 < p`. -/
theorem Zp.negMod_lt {p : Nat} (hp : 0 < p) (a : Nat) :
    Zp.negMod p a < p :=
  Nat.mod_lt _ hp

/-- `negMod p 0 = 0`. -/
theorem Zp.negMod_zero (p : Nat) (hp : 0 < p) :
    Zp.negMod p 0 = 0 := by
  show ((p - 0 % p) % p) = 0
  rw [E213.Tactic.NatHelper.zero_mod p, Nat.sub_zero,
      E213.Meta.Nat.AddMod213.mod_self p]

/-- Smoke: `negMod 5 2 = 3` (since `2 + 3 = 5 ≡ 0 mod 5`). -/
theorem Zp.smoke_negMod_5_2 : Zp.negMod 5 2 = 3 := by decide

/-- Smoke: `negMod 5 4 = 1`. -/
theorem Zp.smoke_negMod_5_4 : Zp.negMod 5 4 = 1 := by decide

/-- PURE `(a * b) / b = a` for `0 < b`. -/
private theorem mul_div_cancel_pure (a b : Nat) (hb : 0 < b) :
    (a * b) / b = a := by
  have hdm := E213.Meta.Nat.AddMod213.div_add_mod (a * b) b
  have hmod : a * b % b = 0 := by
    rw [Nat.mul_comm]
    exact E213.Tactic.NatHelper.mul_mod_right b a
  rw [hmod, Nat.add_zero] at hdm
  -- hdm : b * ((a*b) / b) = a * b
  -- Want: (a*b) / b = a.  Form hdm' : b · (a*b/b) = b · a, then cancel.
  have hdm' : b * ((a * b) / b) = b * a := hdm.trans (Nat.mul_comm a b)
  exact E213.Tactic.NatHelper.mul_left_cancel_pos hb hdm'

/-- For any A, `(A · p^(n+1)) % p^(n+2) = (A % p) · p^(n+1)`. -/
private theorem mul_pow_succ_mod (A p n : Nat) (hp : 0 < p) :
    (A * p^(n + 1)) % p^(n + 2) = (A % p) * p^(n + 1) := by
  rw [Zp.split_mul_pow A p (p^(n + 1))]
  -- A·p^(n+1) = (A%p)·p^(n+1) + (A/p)·(p^(n+1)·p)
  rw [show p^(n + 1) * p = p^(n + 2) from (Nat.pow_succ p (n + 1)).symm]
  -- ((A%p)·p^(n+1) + (A/p)·p^(n+2)) % p^(n+2) = (A%p)·p^(n+1)
  rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]
  -- (A%p)·p^(n+1) % p^(n+2) = (A%p)·p^(n+1)
  have h_lt : (A % p) * p^(n + 1) < p^(n + 2) := by
    have hAp : A % p < p := Nat.mod_lt _ hp
    have hpp : 0 < p^(n + 1) := Nat.pos_pow_of_pos _ hp
    have hlt : (A % p) * p^(n + 1) < p * p^(n + 1) :=
      Nat.mul_lt_mul_of_pos_right hAp hpp
    have hpow : p * p^(n + 1) = p^(n + 2) :=
      (Nat.mul_comm p (p^(n + 1))).trans (Nat.pow_succ p (n + 1)).symm
    rw [hpow] at hlt
    exact hlt
  exact Nat.mod_eq_of_lt h_lt

/-- `negMod` is the additive inverse: `(a + negMod p a) % p = 0` for `0 < p`. -/
private theorem negMod_cancel (p : Nat) (hp : 0 < p) (a : Nat) :
    (a + Zp.negMod p a) % p = 0 := by
  -- Reduce a mod p first using add_mod_left.
  rw [E213.Meta.Nat.AddMod213.add_mod_left hp a (Zp.negMod p a)]
  -- Goal: (a % p + negMod p a) % p = 0
  -- negMod p a := (p - a % p) % p
  show (a % p + (p - a % p) % p) % p = 0
  -- Case on whether a % p = 0.
  cases hr : Nat.decEq (a % p) 0 with
  | isTrue hr0 =>
    rw [hr0, Nat.sub_zero, E213.Meta.Nat.AddMod213.mod_self p,
        Nat.add_zero, E213.Tactic.NatHelper.zero_mod]
  | isFalse hr_ne =>
    have hr_pos : 0 < a % p := Nat.pos_of_ne_zero hr_ne
    have hpa : a % p < p := Nat.mod_lt _ hp
    have hsublt : p - a % p < p := Nat.sub_lt hp hr_pos
    rw [Nat.mod_eq_of_lt hsublt]
    -- Goal: (a % p + (p - a % p)) % p = 0
    have hadd : a % p + (p - a % p) = p := by
      rw [Nat.add_comm]
      exact E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hpa)
    rw [hadd]
    exact E213.Meta.Nat.AddMod213.mod_self p

/-! ## Hensel-lifted inverse sequence

Given `x : ZpSeq p` with `(x.digits 0).val` coprime to `p`
(witnessed by `h_gcd`), construct a sequence of approximate
inverses `invSeq x n : ZpSeq p` such that `invSeq x n` has its
digits 0 through `n` correctly set (and digits beyond `n` are 0),
satisfying:

  `(Zp.mul x (invSeq x n)).trunc (n + 1) = 1 % p^(n + 1)`.

Construction is Hensel: at each step `n → n + 1`, compute the
error `err_n = ((x · invSeq n).trunc (n + 2) - 1) / p^(n + 1) ∈ [0, p)`
and set the new digit `d_n = negMod p (err_n · invDigit0).
Replace digit `(n + 1)` of `invSeq n` with `d_n` to get `invSeq (n+1)`.
-/

/-- Approximate inverse sequence at level `n` — has digits 0..n
    correctly set, digits beyond n are 0. -/
def Zp.invSeq (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) : Nat → ZpSeq p
  | 0 => Zp.invTemplate p hp x h_gcd
  | n + 1 =>
    let prev := Zp.invSeq p hp x h_gcd n
    let i0 := (Zp.invDigit0 p hp x h_gcd).val
    let xy := (Zp.mul p hp x prev).trunc (n + 2)
    let err := (xy - 1) / p^(n + 1)
    let new_digit_val := Zp.negMod p (err * i0)
    ⟨fun j =>
      if j = n + 1 then (⟨new_digit_val, Zp.negMod_lt hp _⟩ : Fin p)
      else prev.digits j⟩

/-- Level-0 of the sequence is the `invTemplate`. -/
theorem Zp.invSeq_zero (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    Zp.invSeq p hp x h_gcd 0 = Zp.invTemplate p hp x h_gcd := rfl

/-- The new digit at level `n + 1` (definitional). -/
theorem Zp.invSeq_succ_new_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    ((Zp.invSeq p hp x h_gcd (n + 1)).digits (n + 1)).val
      = Zp.negMod p
          (((Zp.mul p hp x (Zp.invSeq p hp x h_gcd n)).trunc (n + 2) - 1)
              / p^(n + 1)
            * (Zp.invDigit0 p hp x h_gcd).val) := by
  show (if (n + 1 : Nat) = n + 1 then
          (⟨Zp.negMod p _, Zp.negMod_lt hp _⟩ : Fin p)
        else (Zp.invSeq p hp x h_gcd n).digits (n + 1)).val = _
  rw [if_pos rfl]

/-- Digits below `n + 1` are inherited from the previous level. -/
theorem Zp.invSeq_succ_digit_below (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n j : Nat) (hj : j ≠ n + 1) :
    ((Zp.invSeq p hp x h_gcd (n + 1)).digits j)
      = (Zp.invSeq p hp x h_gcd n).digits j := by
  show (if j = n + 1 then
          (⟨Zp.negMod p _, Zp.negMod_lt hp _⟩ : Fin p)
        else (Zp.invSeq p hp x h_gcd n).digits j) = _
  rw [if_neg hj]

/-- Above level `n`, digits of `invSeq n` are zero. -/
theorem Zp.invSeq_digit_above (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ∀ n k, n < k → ((Zp.invSeq p hp x h_gcd n).digits k).val = 0
  | 0, k, hk => by
    show (if k = 0 then Zp.invDigit0 p hp x h_gcd
          else (⟨0, hp⟩ : Fin p)).val = 0
    rw [if_neg (Nat.ne_of_gt hk)]
  | n + 1, k, hk => by
    have hkne : k ≠ n + 1 := by
      intro heq
      rw [heq] at hk
      exact Nat.lt_irrefl _ hk
    rw [show (Zp.invSeq p hp x h_gcd (n + 1)).digits k
              = (Zp.invSeq p hp x h_gcd n).digits k from
          Zp.invSeq_succ_digit_below p hp x h_gcd n k hkne]
    exact Zp.invSeq_digit_above p hp x h_gcd n k (Nat.lt_of_succ_lt hk)

/-- Truncation at levels `k ≤ n + 1` is preserved when extending
    `invSeq n` to `invSeq (n + 1)` — the new digit only affects
    position `n + 1`, which is outside the trunc bound `k`. -/
theorem Zp.invSeq_succ_trunc_low (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    ∀ k, k ≤ n + 1 →
      (Zp.invSeq p hp x h_gcd (n + 1)).trunc k
        = (Zp.invSeq p hp x h_gcd n).trunc k
  | 0, _ => rfl
  | k + 1, h => by
    have hk : k ≤ n := Nat.le_of_succ_le_succ h
    have hk_ne : k ≠ n + 1 := by
      intro heq
      rw [heq] at hk
      exact Nat.not_succ_le_self n hk
    have ih : (Zp.invSeq p hp x h_gcd (n + 1)).trunc k
              = (Zp.invSeq p hp x h_gcd n).trunc k :=
      Zp.invSeq_succ_trunc_low p hp x h_gcd n k (Nat.le_of_lt h)
    show (Zp.invSeq p hp x h_gcd (n + 1)).trunc k
          + ((Zp.invSeq p hp x h_gcd (n + 1)).digits k).val * p^k
        = (Zp.invSeq p hp x h_gcd n).trunc k
          + ((Zp.invSeq p hp x h_gcd n).digits k).val * p^k
    rw [ih, Zp.invSeq_succ_digit_below p hp x h_gcd n k hk_ne]

/-- `(invSeq n).trunc (n + 2) = (invSeq n).trunc (n + 1)` — extending
    the trunc beyond level `n` doesn't add anything (digit `n+1` is 0). -/
theorem Zp.invSeq_trunc_at_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    (Zp.invSeq p hp x h_gcd n).trunc (n + 2)
      = (Zp.invSeq p hp x h_gcd n).trunc (n + 1) := by
  show (Zp.invSeq p hp x h_gcd n).trunc (n + 1)
        + ((Zp.invSeq p hp x h_gcd n).digits (n + 1)).val * p^(n + 1)
      = (Zp.invSeq p hp x h_gcd n).trunc (n + 1)
  rw [Zp.invSeq_digit_above p hp x h_gcd n (n + 1) (Nat.lt_succ_self n)]
  rw [Nat.zero_mul, Nat.add_zero]

/-- Digit 0 of `invSeq n` is always `invDigit0` (invariant under
    Hensel lifting, since each step only adds digits at position n+1). -/
theorem Zp.invSeq_digit_zero (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ∀ n, ((Zp.invSeq p hp x h_gcd n).digits 0).val
          = (Zp.invDigit0 p hp x h_gcd).val
  | 0 => Zp.invTemplate_digit_zero p hp x h_gcd
  | n + 1 => by
    have hne : (0 : Nat) ≠ n + 1 := fun h => Nat.noConfusion h
    rw [show (Zp.invSeq p hp x h_gcd (n + 1)).digits 0
              = (Zp.invSeq p hp x h_gcd n).digits 0 from
          Zp.invSeq_succ_digit_below p hp x h_gcd n 0 hne]
    exact Zp.invSeq_digit_zero p hp x h_gcd n

/-- `(invSeq n).trunc 1 = invDigit0` for any level `n`. -/
theorem Zp.invSeq_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    (Zp.invSeq p hp x h_gcd n).trunc 1
      = (Zp.invDigit0 p hp x h_gcd).val := by
  show (0 : Nat) + ((Zp.invSeq p hp x h_gcd n).digits 0).val * p^0
      = (Zp.invDigit0 p hp x h_gcd).val
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact Zp.invSeq_digit_zero p hp x h_gcd n

/-- Level-1 Hensel correctness for any approximation: `x · invSeq x n ≡ 1 (mod p)`. -/
theorem Zp.mul_invSeq_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    (Zp.mul p hp x (Zp.invSeq p hp x h_gcd n)).trunc 1 = 1 % p := by
  rw [Zp.mul_trunc p hp x (Zp.invSeq p hp x h_gcd n) 1,
      Zp.invSeq_trunc_one p hp x h_gcd n]
  show ((0 + (x.digits 0).val * p^0) * (Zp.invDigit0 p hp x h_gcd).val) % p^1
      = 1 % p
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one]
  exact Zp.invDigit0_eq p hp x h_gcd

/-- `x.trunc m mod p = (x.digits 0).val mod p` for `m ≥ 1`.  Only digit-0
    contributes mod p; higher digits are multiplied by p^≥1. -/
private theorem trunc_succ_mod_p (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (m : Nat) :
    (x.trunc (m + 1)) % p = (x.digits 0).val % p := by
  induction m with
  | zero =>
    show (0 + (x.digits 0).val * p^0) % p = (x.digits 0).val % p
    rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  | succ k ih =>
    show (x.trunc (k + 1) + (x.digits (k + 1)).val * p^(k + 1)) % p
        = (x.digits 0).val % p
    -- Use add_mod_gen.
    rw [E213.Meta.Nat.AddMod213.add_mod_gen]
    -- ((x.trunc (k+1)) % p + (x_(k+1) · p^(k+1)) % p) % p
    rw [ih]
    -- ((x_0) % p + (x_(k+1) · p^(k+1)) % p) % p = x_0 % p
    -- (x_(k+1) · p^(k+1)) % p: p^(k+1) is divisible by p, so this is 0 mod p.
    have h_mul_mod : ((x.digits (k + 1)).val * p^(k + 1)) % p = 0 := by
      show ((x.digits (k + 1)).val * p^(k + 1)) % p = 0
      rw [show p^(k + 1) = p^k * p from Nat.pow_succ p k]
      rw [show (x.digits (k + 1)).val * (p^k * p)
              = p * ((x.digits (k + 1)).val * p^k) from by
            rw [Nat.mul_comm (p^k) p,
                ← E213.Tactic.NatHelper.mul_assoc
                  (x.digits (k + 1)).val p (p^k),
                Nat.mul_comm ((x.digits (k + 1)).val) p,
                E213.Tactic.NatHelper.mul_assoc
                  p (x.digits (k + 1)).val (p^k)]]
      exact E213.Tactic.NatHelper.mul_mod_right p _
    rw [h_mul_mod, Nat.add_zero]
    exact E213.Tactic.NatHelper.mod_mod_pure _ _

/-- `(invSeq (n+1)).trunc (n + 2) = (invSeq n).trunc (n + 1) +
    new_digit · p^(n+1)` — the extension formula. -/
theorem Zp.invSeq_succ_trunc_extend (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    (Zp.invSeq p hp x h_gcd (n + 1)).trunc (n + 2)
      = (Zp.invSeq p hp x h_gcd n).trunc (n + 1)
          + ((Zp.invSeq p hp x h_gcd (n + 1)).digits (n + 1)).val
              * p^(n + 1) := by
  show (Zp.invSeq p hp x h_gcd (n + 1)).trunc (n + 1)
        + ((Zp.invSeq p hp x h_gcd (n + 1)).digits (n + 1)).val
            * p^(n + 1)
      = (Zp.invSeq p hp x h_gcd n).trunc (n + 1)
          + ((Zp.invSeq p hp x h_gcd (n + 1)).digits (n + 1)).val
              * p^(n + 1)
  rw [Zp.invSeq_succ_trunc_low p hp x h_gcd n (n + 1) (Nat.le_refl _)]

end E213.Lib.Math.Padic
