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

/-- `1 < p^(k+1)` for `1 < p` and any `k`. -/
private theorem one_lt_pow_succ (p : Nat) (hp : 1 < p) (k : Nat) :
    1 < p^(k + 1) := by
  induction k with
  | zero =>
    show 1 < p^1
    rw [Nat.pow_one]; exact hp
  | succ m ih =>
    have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
    have hpm_pos : 0 < p^(m + 1) := Nat.pos_pow_of_pos _ hp_pos
    calc 1 < p^(m + 1) := ih
      _ ≤ p^(m + 1) * p :=
          Nat.le_mul_of_pos_right (p^(m + 1)) hp_pos
      _ = p^(m + 2) := (Nat.pow_succ p (m + 1)).symm

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

/-- Hensel final combinator: given `(e + S % p) ≡ 0 (mod p)` and
    `1 < p^(n+2)`, conclude `(1 + (e + S % p) · p^(n+1)) % p^(n+2) = 1`. -/
private theorem hensel_final (e S p n : Nat) (hp_pow : 1 < p^(n + 2))
    (h_cancel : (e + S % p) % p = 0) :
    (1 + (e + S % p) * p^(n + 1)) % p^(n + 2) = 1 := by
  -- (e + S % p) = ((e + S % p) / p) · p (since the mod is 0).
  have h_q : e + S % p = ((e + S % p) / p) * p := by
    have hdm := E213.Meta.Nat.AddMod213.div_add_mod (e + S % p) p
    rw [h_cancel, Nat.add_zero, Nat.mul_comm] at hdm
    exact hdm.symm
  rw [h_q]
  -- ((e + S % p)/p · p) · p^(n+1) = ((e + S % p)/p) · (p · p^(n+1)) = ... · p^(n+2)
  rw [E213.Tactic.NatHelper.mul_assoc ((e + S % p) / p) p (p^(n + 1))]
  rw [show p * p^(n + 1) = p^(n + 2) from
        (Nat.mul_comm p (p^(n + 1))).trans (Nat.pow_succ p (n + 1)).symm]
  -- (1 + ((e + S % p)/p) · p^(n+2)) % p^(n+2) = 1 % p^(n+2) = 1
  rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]
  exact Nat.mod_eq_of_lt hp_pow

/-- Hensel cancellation: with `(x_0 · i0) ≡ 1 (mod p)`, the
    correction `negMod p (e · i0)` makes `(x_0 · correction)`
    cancel `e` modulo `p`:
        `(e + x_0 · negMod p (e · i0) % p) % p = 0`. -/
private theorem hensel_cancel (p x_0 i0 e_n : Nat) (hp : 1 < p)
    (h_x_i0 : (x_0 * i0) % p = 1 % p) :
    (e_n + (x_0 * Zp.negMod p (e_n * i0)) % p) % p = 0 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  have h_one : 1 % p = 1 := Nat.mod_eq_of_lt hp
  have hcancel : ((e_n * i0) + Zp.negMod p (e_n * i0)) % p = 0 :=
    negMod_cancel p hp' (e_n * i0)
  have hmul : (x_0 * ((e_n * i0) + Zp.negMod p (e_n * i0))) % p = 0 := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure x_0 _ p, hcancel]
    show (x_0 * 0) % p = 0
    rw [Nat.mul_zero]; exact E213.Tactic.NatHelper.zero_mod p
  rw [Nat.mul_add x_0 (e_n * i0) (Zp.negMod p (e_n * i0))] at hmul
  rw [show x_0 * (e_n * i0) = e_n * (x_0 * i0) from by
        rw [← E213.Tactic.NatHelper.mul_assoc x_0 e_n i0,
            Nat.mul_comm x_0 e_n,
            E213.Tactic.NatHelper.mul_assoc e_n x_0 i0]] at hmul
  rw [E213.Meta.Nat.AddMod213.add_mod_gen] at hmul
  rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure e_n (x_0 * i0) p,
      h_x_i0, h_one, Nat.mul_one] at hmul
  rw [← E213.Meta.Nat.AddMod213.add_mod_left hp' e_n
        ((x_0 * Zp.negMod p (e_n * i0)) % p)] at hmul
  exact hmul

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

/-- The Hensel inductive step: given the IH at level n, the next
    digit chosen by `invSeq` makes `(x · invSeq (n+1)).trunc (n+2) = 1`. -/
private theorem hensel_step (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat)
    (ih : (Zp.mul p (Nat.lt_of_succ_lt hp) x
            (Zp.invSeq p (Nat.lt_of_succ_lt hp) x h_gcd n)).trunc (n + 1) = 1) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) x
      (Zp.invSeq p (Nat.lt_of_succ_lt hp) x h_gcd (n + 1))).trunc (n + 2)
        = 1 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  have hpow_pos : 0 < p^(n + 1) := Nat.pos_pow_of_pos _ hp'
  have h_one_lt : 1 < p^(n + 2) := one_lt_pow_succ p hp (n + 1)
  have h1 : (Zp.mul p hp' x (Zp.invSeq p hp' x h_gcd n)).trunc (n + 2)
            = 1 + ((Zp.mul p hp' x
                    (Zp.invSeq p hp' x h_gcd n)).digits (n + 1)).val
                  * p^(n + 1) := by
    show (Zp.mul p hp' x (Zp.invSeq p hp' x h_gcd n)).trunc (n + 1) + _ = _
    rw [ih]
  have h2 : ((Zp.mul p hp' x (Zp.invSeq p hp' x h_gcd n)).trunc (n + 2) - 1)
            / p^(n + 1)
            = ((Zp.mul p hp' x
                  (Zp.invSeq p hp' x h_gcd n)).digits (n + 1)).val := by
    rw [h1, Nat.add_comm 1, E213.Tactic.NatHelper.add_sub_cancel_right]
    exact mul_div_cancel_pure _ _ hpow_pos
  have h3 : ((Zp.invSeq p hp' x h_gcd (n + 1)).digits (n + 1)).val
            = Zp.negMod p
                (((Zp.mul p hp' x (Zp.invSeq p hp' x h_gcd n)).digits (n + 1)).val
                  * (Zp.invDigit0 p hp' x h_gcd).val) := by
    rw [Zp.invSeq_succ_new_digit p hp' x h_gcd n, h2]
  rw [Zp.mul_trunc p hp' x (Zp.invSeq p hp' x h_gcd (n + 1)) (n + 2)]
  rw [Zp.invSeq_succ_trunc_extend p hp' x h_gcd n]
  rw [Nat.mul_add]
  rw [← Zp.invSeq_trunc_at_succ p hp' x h_gcd n]
  rw [E213.Meta.Nat.AddMod213.add_mod_gen]
  rw [← Zp.mul_trunc p hp' x (Zp.invSeq p hp' x h_gcd n) (n + 2)]
  rw [h1]
  -- Regroup x.trunc(n+2) · (new_digit · p^(n+1)) to (x.trunc(n+2) · new_digit) · p^(n+1)
  rw [← E213.Tactic.NatHelper.mul_assoc (x.trunc (n + 2))
        ((Zp.invSeq p hp' x h_gcd (n + 1)).digits (n + 1)).val (p^(n + 1))]
  rw [mul_pow_succ_mod _ p n hp']
  rw [Nat.add_assoc, ← E213.Tactic.NatHelper.add_mul]
  rw [h3]
  rw [show (x.trunc (n + 2)
            * Zp.negMod p
                (((Zp.mul p hp' x (Zp.invSeq p hp' x h_gcd n)).digits (n + 1)).val
                  * (Zp.invDigit0 p hp' x h_gcd).val)) % p
          = ((x.digits 0).val
                * Zp.negMod p
                    (((Zp.mul p hp' x
                        (Zp.invSeq p hp' x h_gcd n)).digits (n + 1)).val
                      * (Zp.invDigit0 p hp' x h_gcd).val)) % p from by
        rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure (x.trunc (n + 2))]
        rw [trunc_succ_mod_p p hp' x (n + 1)]
        rw [← E213.Meta.Nat.MulMod213.mul_mod_left_pure]]
  exact hensel_final _ _ p n h_one_lt
          (hensel_cancel p (x.digits 0).val (Zp.invDigit0 p hp' x h_gcd).val
            _ hp (Zp.invDigit0_eq p hp' x h_gcd))

/-- **General Hensel correctness**: for `1 < p`, any `n`, and
    `x` with digit-0 coprime to `p`, the approximate inverse
    `invSeq n` satisfies `(x · invSeq n).trunc (n + 1) = 1`,
    i.e., `x · invSeq n ≡ 1 (mod p^(n+1))`. -/
theorem Zp.mul_invSeq_correct (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp) x
            (Zp.invSeq p (Nat.lt_of_succ_lt hp) x h_gcd n)).trunc (n + 1) = 1
  | 0 => by
    rw [Zp.mul_invSeq_trunc_one p (Nat.lt_of_succ_lt hp) x h_gcd 0]
    exact Nat.mod_eq_of_lt hp
  | n + 1 =>
    hensel_step p hp x h_gcd n (Zp.mul_invSeq_correct p hp x h_gcd n)

/-! ## The full inverse `invFull`

The approximations `invSeq n` set digits 0..n correctly while
leaving higher digits zero.  Diagonal-extraction —
`invFull.digits k := (invSeq k).digits k` — collects the
"settled" digit at each position into a single `ZpSeq`.  This is
the true multiplicative inverse of `x` (every truncation level
satisfies `x · invFull ≡ 1`).
-/

/-- Digit stability: `(invSeq n).digits j = (invSeq j).digits j` for
    `j ≤ n` — higher-level approximations preserve lower digits. -/
theorem Zp.invSeq_digit_stable (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ∀ n j, j ≤ n →
      (Zp.invSeq p hp x h_gcd n).digits j
        = (Zp.invSeq p hp x h_gcd j).digits j
  | 0, j, h => by
    have hj : j = 0 := Nat.le_zero.mp h
    rw [hj]
  | n + 1, j, h => by
    cases hcase : Nat.decEq j (n + 1) with
    | isTrue heq => rw [heq]
    | isFalse hne =>
      have hjle_n : j ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h hne)
      rw [Zp.invSeq_succ_digit_below p hp x h_gcd n j hne]
      exact Zp.invSeq_digit_stable p hp x h_gcd n j hjle_n

/-- The full inverse `ZpSeq p`: extract each "settled" digit. -/
def Zp.invFull (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) : ZpSeq p where
  digits := fun k => (Zp.invSeq p hp x h_gcd k).digits k

/-- `invFull.trunc (n+1) = (invSeq n).trunc (n+1)` — at level n+1,
    invFull's truncation matches the level-n approximation
    (which has all digits 0..n correctly set). -/
theorem Zp.invFull_trunc_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    ∀ n, (Zp.invFull p hp x h_gcd).trunc (n + 1)
          = (Zp.invSeq p hp x h_gcd n).trunc (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih : (Zp.invFull p hp x h_gcd).trunc (n + 1)
              = (Zp.invSeq p hp x h_gcd n).trunc (n + 1) :=
      Zp.invFull_trunc_succ p hp x h_gcd n
    show (Zp.invFull p hp x h_gcd).trunc (n + 1)
          + ((Zp.invFull p hp x h_gcd).digits (n + 1)).val * p^(n + 1)
        = (Zp.invSeq p hp x h_gcd (n + 1)).trunc (n + 1)
          + ((Zp.invSeq p hp x h_gcd (n + 1)).digits (n + 1)).val * p^(n + 1)
    rw [ih]
    -- (invSeq n).trunc (n+1) → (invSeq (n+1)).trunc (n+1) via ← invSeq_succ_trunc_low.
    rw [← Zp.invSeq_succ_trunc_low p hp x h_gcd n (n + 1) (Nat.le_refl _)]
    -- invFull.digits (n+1) = invSeq (n+1).digits (n+1) by definition (rfl).
    rfl

/-- **Full Hensel correctness**: `x · invFull ≡ 1 (mod p^(n+1))` for all `n`. -/
theorem Zp.mul_invFull_correct (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) x
      (Zp.invFull p (Nat.lt_of_succ_lt hp) x h_gcd)).trunc (n + 1) = 1 := by
  rw [Zp.mul_trunc, Zp.invFull_trunc_succ, ← Zp.mul_trunc]
  exact Zp.mul_invSeq_correct p hp x h_gcd n

/-! ## Hensel for square root — base data

Square-root extraction in `ZpSeq` follows the same Hensel-lift
template as inversion, with `f(y) = y² − x` instead of `f(y) = x·y − 1`.
The derivative `f'(y) = 2y` must be a unit at digit 0, requiring
`(2 · d_0)` coprime to `p` — automatic for odd `p` when `d_0 ≠ 0`,
delicate for `p = 2`.

`SqrtBase x` packages the digit-0 data: a candidate square root
`d_0` with `d_0² ≡ x.digits 0 (mod p)`, plus the modular inverse
of `2 · d_0` (for the correction formula).
-/

/-- Base data for square-root Hensel lifting: digit-0 square root
    `d_0` with `d_0² ≡ x.digits 0 (mod p)`, plus `(2 · d_0)⁻¹ mod p`. -/
structure Zp.SqrtBase (p : Nat) (x : ZpSeq p) : Type where
  d_0          : Nat
  d_0_lt       : d_0 < p
  sq_eq        : (d_0 * d_0) % p = (x.digits 0).val % p
  two_d_0_inv  : Nat
  two_d_0_inv_lt : two_d_0_inv < p
  two_d_0_inv_eq : (2 * d_0 * two_d_0_inv) % p = 1 % p

/-- Smoke: for p = 5, x = the constant-4 sequence, the digit-0
    square root is `d_0 = 2` (since 2² = 4 ≡ 4 mod 5).  And
    `2 · 2 = 4`, with `4 · 4 = 16 ≡ 1 mod 5`, so `(2·2)⁻¹ = 4 mod 5`. -/
example : Zp.SqrtBase 5 ⟨fun _ => ⟨4, by decide⟩⟩ where
  d_0 := 2
  d_0_lt := by decide
  sq_eq := by decide
  two_d_0_inv := 4
  two_d_0_inv_lt := by decide
  two_d_0_inv_eq := by decide

/-- **√(-1) in ℤ_5 exists**.  Concrete `SqrtBase` for `neg_one`
    with `d_0 = 2` (since `2² = 4 ≡ -1 (mod 5)`).  Inverse of `2·2`
    is `4` since `4·4 = 16 ≡ 1 (mod 5)`.

    Mathematically: -1 is a quadratic residue mod 5, since the
    quadratic residues mod 5 are `{1, 4}` and `4 ≡ -1`.  This makes
    `ℤ_5` contain `i = √(-1)`, unlike `ℝ`. -/
def Zp.sqrtBase_neg_one_5 : Zp.SqrtBase 5 (ZpSeq.neg_one 5 (by decide)) where
  d_0 := 2
  d_0_lt := by decide
  sq_eq := by decide
  two_d_0_inv := 4
  two_d_0_inv_lt := by decide
  two_d_0_inv_eq := by decide

/-- **√(-1) in ℤ_13 exists**.  `d_0 = 5` (since `5² = 25 ≡ -1 mod 13`).
    `(2·5)⁻¹ = 10⁻¹ = 4` (since `10·4 = 40 ≡ 1 mod 13`). -/
def Zp.sqrtBase_neg_one_13 : Zp.SqrtBase 13 (ZpSeq.neg_one 13 (by decide)) where
  d_0 := 5
  d_0_lt := by decide
  sq_eq := by decide
  two_d_0_inv := 4
  two_d_0_inv_lt := by decide
  two_d_0_inv_eq := by decide

/-- **√2 in ℤ_7 exists**.  `d_0 = 3` (since `3² = 9 ≡ 2 mod 7`).
    `(2·3)⁻¹ = 6⁻¹ = 6` (since `6·6 = 36 ≡ 1 mod 7`).

    The 7-adic integer `√2`: contrasts with `ℝ` where √2 is
    irrational; in ℤ_7 it's an honest p-adic integer with
    digit 0 = 3. -/
def Zp.sqrtBase_two_7 :
    Zp.SqrtBase 7 ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩ where
  d_0 := 3
  d_0_lt := by decide
  sq_eq := by decide
  two_d_0_inv := 6
  two_d_0_inv_lt := by decide
  two_d_0_inv_eq := by decide

/-! ## Sqrt iteration

`sqrtSeq n` is the Hensel-lifted square-root approximation, correct
mod `p^(n+1)`.  At each level, the next digit corrects the residue
`(prev² - x) / p^(n+1) ∈ [0, p)` via the formula
`d_{n+1} = negMod p (err · (2·d_0)⁻¹)`, parallel to `invSeq`.

The signed difference is taken modulo `p^(n+2)` via the Nat
identity `(a + (M - b)) % M = (a - b) mod M` (well-defined since
`b < M = p^(n+2)`).
-/

/-- Approximate `√x` at level `n` — digit 0 is `sb.d_0`, higher
    digits computed by Hensel correction. -/
def Zp.sqrtSeq (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) : Nat → ZpSeq p
  | 0 => ⟨fun k => if k = 0 then ⟨sb.d_0, sb.d_0_lt⟩ else ⟨0, hp⟩⟩
  | n + 1 =>
    let prev := Zp.sqrtSeq p hp x sb n
    let sq := (Zp.mul p hp prev prev).trunc (n + 2)
    let xt := x.trunc (n + 2)
    let diff := (sq + (p^(n + 2) - xt)) % p^(n + 2)
    let err := diff / p^(n + 1)
    let new_digit_val := Zp.negMod p (err * sb.two_d_0_inv)
    ⟨fun j =>
      if j = n + 1 then (⟨new_digit_val, Zp.negMod_lt hp _⟩ : Fin p)
      else prev.digits j⟩

/-- Digit-0 of `sqrtSeq 0` is `sb.d_0`. -/
theorem Zp.sqrtSeq_zero_digit_zero (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    ((Zp.sqrtSeq p hp x sb 0).digits 0).val = sb.d_0 := by
  show (if (0 : Nat) = 0 then (⟨sb.d_0, sb.d_0_lt⟩ : Fin p)
        else (⟨0, hp⟩ : Fin p)).val = sb.d_0
  rw [if_pos rfl]

/-- For `k > 0`, digit-k of `sqrtSeq 0` is 0. -/
theorem Zp.sqrtSeq_zero_digit_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (k : Nat) :
    ((Zp.sqrtSeq p hp x sb 0).digits (k + 1)).val = 0 := by
  show (if (k + 1 : Nat) = 0 then (⟨sb.d_0, sb.d_0_lt⟩ : Fin p)
        else (⟨0, hp⟩ : Fin p)).val = 0
  rw [if_neg (fun h => Nat.noConfusion h)]

/-- `(sqrtSeq 0).trunc 1 = sb.d_0`. -/
theorem Zp.sqrtSeq_zero_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    (Zp.sqrtSeq p hp x sb 0).trunc 1 = sb.d_0 := by
  show (0 : Nat) + ((Zp.sqrtSeq p hp x sb 0).digits 0).val * p^0 = sb.d_0
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact Zp.sqrtSeq_zero_digit_zero p hp x sb

/-- **Level-1 sqrt correctness**: `(sqrtSeq 0)² ≡ x (mod p)`.  This is
    the base case of the Hensel induction — by construction, `sb.d_0`
    satisfies `d_0² ≡ (x.digits 0) (mod p)`, which we read off as
    `(sqrtSeq 0 · sqrtSeq 0).trunc 1 = x.trunc 1 mod p`. -/
theorem Zp.sqr_sqrtSeq_zero_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    (Zp.mul p hp (Zp.sqrtSeq p hp x sb 0) (Zp.sqrtSeq p hp x sb 0)).trunc 1
      = (x.trunc 1) % p := by
  rw [Zp.mul_trunc p hp _ _ 1, Zp.sqrtSeq_zero_trunc_one p hp x sb]
  rw [Nat.pow_one]
  show (sb.d_0 * sb.d_0) % p
      = ((0 : Nat) + (x.digits 0).val * p^0) % p
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact sb.sq_eq

/-! ### Structural lemmas for `sqrtSeq` (parallel to `invSeq`) -/

/-- The new digit at level `n + 1` (definitional). -/
theorem Zp.sqrtSeq_succ_new_digit (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    ((Zp.sqrtSeq p hp x sb (n + 1)).digits (n + 1)).val
      = Zp.negMod p
          (((Zp.mul p hp (Zp.sqrtSeq p hp x sb n) (Zp.sqrtSeq p hp x sb n)).trunc (n + 2)
                + (p^(n + 2) - x.trunc (n + 2))) % p^(n + 2)
              / p^(n + 1)
            * sb.two_d_0_inv) := by
  show (if (n + 1 : Nat) = n + 1 then
          (⟨Zp.negMod p _, Zp.negMod_lt hp _⟩ : Fin p)
        else (Zp.sqrtSeq p hp x sb n).digits (n + 1)).val = _
  rw [if_pos rfl]

/-- Digits below `n + 1` are inherited from the previous level. -/
theorem Zp.sqrtSeq_succ_digit_below (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n j : Nat) (hj : j ≠ n + 1) :
    ((Zp.sqrtSeq p hp x sb (n + 1)).digits j)
      = (Zp.sqrtSeq p hp x sb n).digits j := by
  show (if j = n + 1 then
          (⟨Zp.negMod p _, Zp.negMod_lt hp _⟩ : Fin p)
        else (Zp.sqrtSeq p hp x sb n).digits j) = _
  rw [if_neg hj]

/-- Above level `n`, digits of `sqrtSeq n` are zero. -/
theorem Zp.sqrtSeq_digit_above (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    ∀ n k, n < k → ((Zp.sqrtSeq p hp x sb n).digits k).val = 0
  | 0, k, hk => by
    show (if k = 0 then (⟨sb.d_0, sb.d_0_lt⟩ : Fin p)
          else (⟨0, hp⟩ : Fin p)).val = 0
    rw [if_neg (Nat.ne_of_gt hk)]
  | n + 1, k, hk => by
    have hkne : k ≠ n + 1 := by
      intro heq
      rw [heq] at hk
      exact Nat.lt_irrefl _ hk
    rw [show (Zp.sqrtSeq p hp x sb (n + 1)).digits k
              = (Zp.sqrtSeq p hp x sb n).digits k from
          Zp.sqrtSeq_succ_digit_below p hp x sb n k hkne]
    exact Zp.sqrtSeq_digit_above p hp x sb n k (Nat.lt_of_succ_lt hk)

/-- Truncation at levels `k ≤ n + 1` is preserved when extending
    `sqrtSeq n` to `sqrtSeq (n + 1)`. -/
theorem Zp.sqrtSeq_succ_trunc_low (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    ∀ k, k ≤ n + 1 →
      (Zp.sqrtSeq p hp x sb (n + 1)).trunc k
        = (Zp.sqrtSeq p hp x sb n).trunc k
  | 0, _ => rfl
  | k + 1, h => by
    have hk : k ≤ n := Nat.le_of_succ_le_succ h
    have hk_ne : k ≠ n + 1 := by
      intro heq
      rw [heq] at hk
      exact Nat.not_succ_le_self n hk
    have ih : (Zp.sqrtSeq p hp x sb (n + 1)).trunc k
              = (Zp.sqrtSeq p hp x sb n).trunc k :=
      Zp.sqrtSeq_succ_trunc_low p hp x sb n k (Nat.le_of_lt h)
    show (Zp.sqrtSeq p hp x sb (n + 1)).trunc k
          + ((Zp.sqrtSeq p hp x sb (n + 1)).digits k).val * p^k
        = (Zp.sqrtSeq p hp x sb n).trunc k
          + ((Zp.sqrtSeq p hp x sb n).digits k).val * p^k
    rw [ih, Zp.sqrtSeq_succ_digit_below p hp x sb n k hk_ne]

/-- `(sqrtSeq n).trunc (n + 2) = (sqrtSeq n).trunc (n + 1)` — digit
    at position `n + 1` of `sqrtSeq n` is zero (only `sqrtSeq (n+1)`
    sets it). -/
theorem Zp.sqrtSeq_trunc_at_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    (Zp.sqrtSeq p hp x sb n).trunc (n + 2)
      = (Zp.sqrtSeq p hp x sb n).trunc (n + 1) := by
  show (Zp.sqrtSeq p hp x sb n).trunc (n + 1)
        + ((Zp.sqrtSeq p hp x sb n).digits (n + 1)).val * p^(n + 1)
      = (Zp.sqrtSeq p hp x sb n).trunc (n + 1)
  rw [Zp.sqrtSeq_digit_above p hp x sb n (n + 1) (Nat.lt_succ_self n)]
  rw [Nat.zero_mul, Nat.add_zero]

/-- Digit 0 of `sqrtSeq n` is always `sb.d_0` (Hensel invariant —
    each lifting step adds digits at position `n + 1` only). -/
theorem Zp.sqrtSeq_digit_zero (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    ∀ n, ((Zp.sqrtSeq p hp x sb n).digits 0).val = sb.d_0
  | 0 => Zp.sqrtSeq_zero_digit_zero p hp x sb
  | n + 1 => by
    have hne : (0 : Nat) ≠ n + 1 := fun h => Nat.noConfusion h
    rw [show (Zp.sqrtSeq p hp x sb (n + 1)).digits 0
              = (Zp.sqrtSeq p hp x sb n).digits 0 from
          Zp.sqrtSeq_succ_digit_below p hp x sb n 0 hne]
    exact Zp.sqrtSeq_digit_zero p hp x sb n

/-- `(sqrtSeq n).trunc 1 = sb.d_0` for any level `n`. -/
theorem Zp.sqrtSeq_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    (Zp.sqrtSeq p hp x sb n).trunc 1 = sb.d_0 := by
  show (0 : Nat) + ((Zp.sqrtSeq p hp x sb n).digits 0).val * p^0 = sb.d_0
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact Zp.sqrtSeq_digit_zero p hp x sb n

/-- Level-1 sqrt correctness for any approximation:
    `(sqrtSeq n)² ≡ x (mod p)`.  Reduces to `sb.sq_eq` via
    `sqrtSeq_trunc_one`. -/
theorem Zp.sqr_sqrtSeq_trunc_one (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    (Zp.mul p hp (Zp.sqrtSeq p hp x sb n) (Zp.sqrtSeq p hp x sb n)).trunc 1
      = (x.trunc 1) % p := by
  rw [Zp.mul_trunc p hp _ _ 1, Zp.sqrtSeq_trunc_one p hp x sb n]
  rw [Nat.pow_one]
  show (sb.d_0 * sb.d_0) % p
      = ((0 : Nat) + (x.digits 0).val * p^0) % p
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact sb.sq_eq

/-- `(sqrtSeq (n+1)).trunc (n+2) = (sqrtSeq n).trunc (n+1) + d · p^(n+1)`
    where `d` is the new digit at position `n+1`.  The Hensel extension
    formula for sqrt. -/
theorem Zp.sqrtSeq_succ_trunc_extend (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    (Zp.sqrtSeq p hp x sb (n + 1)).trunc (n + 2)
      = (Zp.sqrtSeq p hp x sb n).trunc (n + 1)
          + ((Zp.sqrtSeq p hp x sb (n + 1)).digits (n + 1)).val
              * p^(n + 1) := by
  show (Zp.sqrtSeq p hp x sb (n + 1)).trunc (n + 1)
        + ((Zp.sqrtSeq p hp x sb (n + 1)).digits (n + 1)).val
            * p^(n + 1)
      = (Zp.sqrtSeq p hp x sb n).trunc (n + 1)
          + ((Zp.sqrtSeq p hp x sb (n + 1)).digits (n + 1)).val
              * p^(n + 1)
  rw [Zp.sqrtSeq_succ_trunc_low p hp x sb n (n + 1) (Nat.le_refl _)]

/-! ### Helpers for sqrt induction

The full Hensel sqrt correctness uses three algebraic helpers:

1. `pow_n1_sq_eq_pow_n2_mul_pow_n`: `p^(n+1)·p^(n+1) = p^n · p^(n+2)`.
   The key identity making `K² ≡ 0 (mod M)` work where
   `K = p^(n+1)`, `M = p^(n+2)`.
2. `K_sq_mod_M_zero`: `p^(n+1)·p^(n+1) % p^(n+2) = 0`.
3. `binomial_sq_mod_pure`: `(a + d·K)² mod M = (a² + 2·a·d·K) mod M`
   given `K² mod M = 0`.
-/

/-- PURE: `p^n · p^m = p^(n + m)` by induction on `m`. -/
private theorem pow_add_pure_hensel (p : Nat) :
    ∀ n m, p^n * p^m = p^(n + m)
  | _, 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n, m + 1 => by
    rw [Nat.pow_succ, ← E213.Tactic.NatHelper.mul_assoc,
        pow_add_pure_hensel p n m]
    show p^(n + m) * p = p^(n + (m + 1))
    rw [← Nat.add_assoc, ← Nat.pow_succ]

/-- PURE: `p^(n+1) · p^(n+1) = p^n · p^(n+2)`. -/
private theorem pow_n1_sq_eq_pow_n2_mul_pow_n (p n : Nat) :
    p^(n + 1) * p^(n + 1) = p^n * p^(n + 2) := by
  rw [pow_add_pure_hensel p (n + 1) (n + 1),
      pow_add_pure_hensel p n (n + 2)]
  -- Goal: p^(n+1+(n+1)) = p^(n+(n+2))
  show p^(n + 1 + (n + 1)) = p^(n + (n + 2))
  -- Reduce exponents: n + 1 + (n + 1) = n + (n + 2).
  have hsum : n + 1 + (n + 1) = n + (n + 2) := by
    rw [Nat.add_assoc n 1 (n + 1), Nat.add_comm 1 (n + 1)]
  rw [hsum]

/-- PURE: `K² mod M = 0` where `K = p^(n+1)`, `M = p^(n+2)`. -/
private theorem K_sq_mod_M_zero (p n : Nat) :
    p^(n + 1) * p^(n + 1) % p^(n + 2) = 0 := by
  rw [pow_n1_sq_eq_pow_n2_mul_pow_n p n]
  -- p^n · p^(n+2) % p^(n+2) = 0
  rw [Nat.mul_comm]
  exact E213.Tactic.NatHelper.mul_mod_right (p^(n + 2)) (p^n)

/-- PURE: `(a + b)² = a·a + (a·b + a·b) + b·b`. -/
private theorem binomial_sq_expand (a b : Nat) :
    (a + b) * (a + b) = a * a + (a * b + a * b) + b * b := by
  -- (a+b)·(a+b) = (a+b)·a + (a+b)·b  [Nat.mul_add]
  rw [Nat.mul_add (a + b) a b]
  -- = a·a + b·a + ((a+b)·b)
  rw [E213.Tactic.NatHelper.add_mul a b a,
      E213.Tactic.NatHelper.add_mul a b b]
  -- a·a + b·a + (a·b + b·b)
  rw [Nat.mul_comm b a]
  -- a·a + a·b + (a·b + b·b)
  rw [Nat.add_assoc (a * a) (a * b) (a * b + b * b),
      ← Nat.add_assoc (a * b) (a * b) (b * b),
      ← Nat.add_assoc (a * a) (a * b + a * b) (b * b)]

/-- PURE: `(d·K) · (d·K) = (d·d) · (K·K)`. -/
private theorem mul_sq_swap (d K : Nat) :
    (d * K) * (d * K) = (d * d) * (K * K) := by
  rw [E213.Tactic.NatHelper.mul_assoc d K (d * K)]
  -- d · (K · (d · K)) = d · (d · (K · K))
  -- K · (d · K) = d · (K · K) by mul_comm + mul_assoc
  rw [show K * (d * K) = d * (K * K) by
        rw [← E213.Tactic.NatHelper.mul_assoc K d K, Nat.mul_comm K d,
            E213.Tactic.NatHelper.mul_assoc d K K]]
  rw [← E213.Tactic.NatHelper.mul_assoc d d (K * K)]

/-- PURE binomial: `(a + d·K)² mod M = (a² + 2·(a·d·K)) mod M`
    given `K² mod M = 0`. -/
private theorem binomial_sq_mod_pure (a d K M : Nat) (hM : 0 < M)
    (hK : K * K % M = 0) :
    (a + d * K) * (a + d * K) % M
      = (a * a + 2 * (a * d * K)) % M := by
  rw [binomial_sq_expand a (d * K)]
  -- LHS = (a·a + (a·(d·K) + a·(d·K)) + (d·K)·(d·K)) % M
  rw [mul_sq_swap d K]
  -- LHS = (a·a + (a·(d·K) + a·(d·K)) + (d·d)·(K·K)) % M
  -- The (d·d)·(K·K) term: mod M = 0.
  have h_zero : ((d * d) * (K * K)) % M = 0 := by
    rw [Nat.mul_comm (d * d) (K * K),
        E213.Meta.Nat.MulMod213.mul_mod_left_pure (K * K) (d * d) M,
        hK, Nat.zero_mul, E213.Tactic.NatHelper.zero_mod]
  -- Strip the d²·K² term mod M.
  rw [E213.Meta.Nat.AddMod213.add_mod hM
        (a * a + (a * (d * K) + a * (d * K))) ((d * d) * (K * K))]
  rw [h_zero, Nat.add_zero, E213.Tactic.NatHelper.mod_mod_pure]
  -- Goal: (a·a + (a·(d·K) + a·(d·K))) % M = (a·a + 2·(a·d·K)) % M
  -- Show a·(d·K) = a·d·K by mul_assoc, and a·d·K + a·d·K = 2·(a·d·K).
  rw [← E213.Tactic.NatHelper.mul_assoc a d K]
  -- Goal: (a·a + (a·d·K + a·d·K)) % M = (a·a + 2·(a·d·K)) % M
  rw [← Nat.two_mul (a * d * K)]

/-- PURE: `(X + Y) % p = 0 → ∀ c, (c·X + c·Y) % p = 0`. -/
private theorem scale_mod (p c X Y : Nat) (h : (X + Y) % p = 0) :
    (c * X + c * Y) % p = 0 := by
  rw [← Nat.mul_add c X Y,
      E213.Meta.Nat.MulMod213.mul_mod_right_pure c (X + Y) p,
      h, Nat.mul_zero, E213.Tactic.NatHelper.zero_mod]

/-- PURE: replace `A` in `(A + B) % p` by `A'` with same mod-p residue. -/
private theorem add_mod_swap_left (p A A' B : Nat) (hp : 0 < p)
    (h : (A + B) % p = 0) (heq : A % p = A' % p) :
    (A' + B) % p = 0 := by
  rw [E213.Meta.Nat.AddMod213.add_mod hp A' B]
  rw [← heq, ← E213.Meta.Nat.AddMod213.add_mod hp A B]
  exact h

/-- PURE: replace `B` in `(A + B) % p` by `B'` with same mod-p residue. -/
private theorem add_mod_swap_right (p A B B' : Nat) (hp : 0 < p)
    (h : (A + B) % p = 0) (heq : B % p = B' % p) :
    (A + B') % p = 0 := by
  rw [E213.Meta.Nat.AddMod213.add_mod hp A B']
  rw [← heq, ← E213.Meta.Nat.AddMod213.add_mod hp A B]
  exact h

/-- PURE sqrt cancellation: given `a ≡ d_0 (mod p)`,
    `2·d_0·two_d_0_inv ≡ 1 (mod p)`, and `(err·two_d_0_inv + d) ≡ 0 (mod p)`,
    we get `(err + 2·a·d) % p = 0`.  This is the algebraic core of
    the Hensel sqrt cancellation. -/
private theorem sqrt_cancel (p : Nat) (hp : 0 < p)
    (a err d_0 two_d_0_inv d : Nat)
    (h_a_mod : a % p = d_0 % p)
    (h_inv_eq : (2 * d_0 * two_d_0_inv) % p = 1 % p)
    (h_d_neg : (err * two_d_0_inv + d) % p = 0) :
    (err + 2 * a * d) % p = 0 := by
  -- Step 1: scale h_d_neg by 2·d_0.
  have h_scale : (2 * d_0 * (err * two_d_0_inv) + 2 * d_0 * d) % p = 0 :=
    scale_mod p (2 * d_0) (err * two_d_0_inv) d h_d_neg
  -- Step 2: reorder 2·d_0·(err·two_d_0_inv) → err·(2·d_0·two_d_0_inv).
  have h_reorder : 2 * d_0 * (err * two_d_0_inv)
                   = err * (2 * d_0 * two_d_0_inv) := by
    rw [← E213.Tactic.NatHelper.mul_assoc (2 * d_0) err two_d_0_inv,
        Nat.mul_comm (2 * d_0) err,
        E213.Tactic.NatHelper.mul_assoc err (2 * d_0) two_d_0_inv]
  rw [h_reorder] at h_scale
  -- Step 3: in mod-p, (err·(2·d_0·two_d_0_inv)) ≡ err (using h_inv_eq).
  have h_rw1 : (err * (2 * d_0 * two_d_0_inv)) % p = err % p := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure err _ p, h_inv_eq,
        ← E213.Meta.Nat.MulMod213.mul_mod_right_pure err 1 p,
        Nat.mul_one]
  have h_step3 : (err + 2 * d_0 * d) % p = 0 :=
    add_mod_swap_left p _ err (2 * d_0 * d) hp h_scale h_rw1
  -- Step 4: in mod-p, (2·d_0·d) ≡ (2·a·d) using h_a_mod.
  have h_rw2 : (2 * d_0 * d) % p = (2 * a * d) % p := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure (2 * d_0) d p,
        E213.Meta.Nat.MulMod213.mul_mod_left_pure (2 * a) d p]
    rw [show (2 * d_0) % p = (2 * a) % p by
          rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure 2 d_0 p,
              E213.Meta.Nat.MulMod213.mul_mod_right_pure 2 a p,
              h_a_mod]]
  exact add_mod_swap_right p err (2 * d_0 * d) (2 * a * d) hp h_step3 h_rw2

/-- PURE: `x.trunc (n+2) % p^(n+1) = x.trunc (n+1)`.  Higher digit
    is killed by the mod, and `trunc (n+1) < p^(n+1)`. -/
private theorem trunc_succ_mod_K (p : Nat) (hp : 0 < p) (x : ZpSeq p) (n : Nat) :
    x.trunc (n + 2) % p^(n + 1) = x.trunc (n + 1) := by
  show (x.trunc (n + 1) + (x.digits (n + 1)).val * p^(n + 1)) % p^(n + 1)
       = x.trunc (n + 1)
  rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]
  exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow hp x (n + 1))

/-- PURE: `M % K = 0` where `K = p^(n+1)`, `M = p^(n+2)`. -/
private theorem M_mod_K_zero (p n : Nat) : p^(n + 2) % p^(n + 1) = 0 := by
  rw [show p^(n + 2) = p^(n + 1) * p from Nat.pow_succ p (n + 1)]
  exact E213.Tactic.NatHelper.mul_mod_right (p^(n + 1)) p

/-- PURE: `K ∣ M` where `K = p^(n+1)`, `M = p^(n+2)`. -/
private theorem K_dvd_M (p n : Nat) : p^(n + 1) ∣ p^(n + 2) :=
  ⟨p, (Nat.pow_succ p (n + 1)).symm⟩

/-- PURE: given `s % K = xt % K`, `xt < M = K · p`, derive
    `(s + (M - xt)) % K = 0`.  Used to extract `err = ((s + M - xt) % M) / K`. -/
private theorem add_neg_mod_K_zero (p n s xt : Nat) (hp : 0 < p)
    (hxt : xt < p^(n + 2)) (h_eq : s % p^(n + 1) = xt % p^(n + 1)) :
    (s + (p^(n + 2) - xt)) % p^(n + 1) = 0 := by
  have hK_pos : 0 < p^(n + 1) := Nat.pos_pow_of_pos _ hp
  rw [E213.Meta.Nat.AddMod213.add_mod hK_pos s (p^(n + 2) - xt), h_eq]
  rw [← E213.Meta.Nat.AddMod213.add_mod hK_pos xt (p^(n + 2) - xt)]
  rw [E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hxt)]
  exact M_mod_K_zero p n

/-- PURE: if `xt < M` and `(Z + (M - xt)) % M = 0`, then `Z % M = xt`. -/
private theorem mod_eq_from_neg_eq (M Z xt : Nat) (hM : 0 < M) (hxt : xt < M)
    (h : (Z + (M - xt)) % M = 0) : Z % M = xt := by
  have h_chain : ((Z + (M - xt)) + xt) % M = xt := by
    rw [E213.Meta.Nat.AddMod213.add_mod_gen,
        h, Nat.zero_add, E213.Tactic.NatHelper.mod_mod_pure,
        Nat.mod_eq_of_lt hxt]
  have h_rear : (Z + (M - xt)) + xt = Z + M := by
    rw [Nat.add_assoc Z (M - xt) xt, Nat.add_comm (M - xt) xt,
        E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hxt)]
  rw [h_rear] at h_chain
  rw [Nat.add_comm Z M, E213.Meta.Nat.AddMod213.add_mod_left hM M Z,
      E213.Meta.Nat.AddMod213.mod_self M, Nat.zero_add] at h_chain
  exact h_chain

/-- `(Zp.mul (sqrtSeq n) (sqrtSeq n)).trunc (n + 2) = (a * a) % p^(n+2)`
    where `a = (sqrtSeq n).trunc (n + 1)`.  Uses `sqrtSeq_trunc_at_succ`
    to collapse `trunc (n + 2) = trunc (n + 1)` for the input. -/
private theorem prev_sq_trunc_form (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    (Zp.mul p hp (Zp.sqrtSeq p hp x sb n) (Zp.sqrtSeq p hp x sb n)).trunc (n + 2)
      = ((Zp.sqrtSeq p hp x sb n).trunc (n + 1)
          * (Zp.sqrtSeq p hp x sb n).trunc (n + 1)) % p^(n + 2) := by
  rw [Zp.mul_trunc p hp _ _ (n + 2), Zp.sqrtSeq_trunc_at_succ p hp x sb n]

/-- PURE: the abstract sqrt Hensel step.  Given `a`, `xt`, `d_0`,
    `two_d_0_inv`, `err`, `d` satisfying:
    - `(a*a) % K = xt % K` (IH after mul_trunc)
    - `a % p = d_0 % p` (sqrtSeq digit-0 invariant)
    - `(2*d_0*two_d_0_inv) % p = 1 % p` (SqrtBase guarantee)
    - `err = ((a*a + (M-xt)) % M) / K` (sqrtSeq err definition)
    - `d = negMod p (err * two_d_0_inv)` (sqrtSeq new digit)
    Conclude: `((a + d*K) * (a + d*K)) % M = xt`.
    where `K = p^(n+1)`, `M = p^(n+2)`. -/
private theorem sqrt_cancel_full (p : Nat) (hp : 1 < p) (n : Nat)
    (a xt d_0 two_d_0_inv err d : Nat)
    (hxt : xt < p^(n + 2))
    (h_aa_K : (a * a) % p^(n + 1) = xt % p^(n + 1))
    (h_a_mod : a % p = d_0 % p)
    (h_inv_eq : (2 * d_0 * two_d_0_inv) % p = 1 % p)
    (h_err : err = ((a * a + (p^(n + 2) - xt)) % p^(n + 2)) / p^(n + 1))
    (h_d : d = Zp.negMod p (err * two_d_0_inv)) :
    ((a + d * p^(n + 1)) * (a + d * p^(n + 1))) % p^(n + 2) = xt := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  have hM_pos : 0 < p^(n + 2) := Nat.pos_pow_of_pos _ hp'
  -- Step 1: binomial expansion.
  rw [binomial_sq_mod_pure a d (p^(n + 1)) (p^(n + 2)) hM_pos
        (K_sq_mod_M_zero p n)]
  -- Goal: (a*a + 2*(a*d*K)) % M = xt
  apply mod_eq_from_neg_eq (p^(n + 2)) _ _ hM_pos hxt
  -- Goal: ((a*a + 2*(a*d*K)) + (M - xt)) % M = 0
  -- Step 2: rearrange to ((a*a + (M-xt)) + 2*(a*d*K)) % M = 0.
  have h_rearr : a * a + 2 * (a * d * p^(n + 1)) + (p^(n + 2) - xt)
              = (a * a + (p^(n + 2) - xt)) + 2 * (a * d * p^(n + 1)) := by
    rw [Nat.add_assoc (a * a) (2 * (a * d * p^(n + 1))) (p^(n + 2) - xt),
        Nat.add_comm (2 * (a * d * p^(n + 1))) (p^(n + 2) - xt),
        ← Nat.add_assoc]
  rw [h_rearr]
  -- Step 3: derive (a*a + (M - xt)) % K = 0.
  have h_diff_K : (a * a + (p^(n + 2) - xt)) % p^(n + 1) = 0 :=
    add_neg_mod_K_zero p n (a * a) xt hp' hxt h_aa_K
  -- Step 4: (a*a + (M - xt)) % M % K = 0 by mod_mod_of_dvd.
  have h_diff_M_K : ((a * a + (p^(n + 2) - xt)) % p^(n + 2)) % p^(n + 1) = 0 := by
    rw [E213.Meta.Nat.AddMod213.mod_mod_of_dvd _ (K_dvd_M p n)]
    exact h_diff_K
  -- Step 5: diff_M = err * K where err = diff_M / K.
  have h_diff_eq_err_K : (a * a + (p^(n + 2) - xt)) % p^(n + 2)
                       = err * p^(n + 1) := by
    have hdm := E213.Meta.Nat.AddMod213.div_add_mod
                  ((a * a + (p^(n + 2) - xt)) % p^(n + 2)) (p^(n + 1))
    rw [h_diff_M_K, Nat.add_zero, Nat.mul_comm] at hdm
    rw [← hdm, ← h_err]
  -- Step 6: sqrt_cancel gives (err + 2*a*d) % p = 0.
  have h_d_neg : (err * two_d_0_inv + d) % p = 0 := by
    rw [h_d]; exact negMod_cancel p hp' (err * two_d_0_inv)
  have h_cancel : (err + 2 * a * d) % p = 0 :=
    sqrt_cancel p hp' a err d_0 two_d_0_inv d h_a_mod h_inv_eq h_d_neg
  -- Step 7: use add_mod_left to absorb (a*a + (M-xt)) into diff_M.
  rw [E213.Meta.Nat.AddMod213.add_mod_left hM_pos
        (a * a + (p^(n + 2) - xt)) (2 * (a * d * p^(n + 1)))]
  -- Goal: ((a*a + (M-xt)) % M + 2*(a*d*K)) % M = 0
  rw [h_diff_eq_err_K]
  -- Goal: (err*K + 2*(a*d*K)) % M = 0
  -- Reshape: 2*(a*d*K) = (2*a*d)*K, then err*K + (2*a*d)*K = (err + 2*a*d)*K.
  rw [show 2 * (a * d * p^(n + 1)) = 2 * a * d * p^(n + 1) by
        rw [← E213.Tactic.NatHelper.mul_assoc 2 (a * d) (p^(n + 1)),
            ← E213.Tactic.NatHelper.mul_assoc 2 a d]]
  rw [← E213.Tactic.NatHelper.add_mul err (2 * a * d) (p^(n + 1))]
  -- Goal: ((err + 2*a*d) * p^(n+1)) % p^(n+2) = 0
  rw [mul_pow_succ_mod (err + 2 * a * d) p n hp', h_cancel,
      Nat.zero_mul]

/-- **General Hensel sqrt correctness**: for `1 < p`, any `n`, and
    `x` with a valid `SqrtBase` `sb`, the approximate sqrt
    `sqrtSeq n` satisfies `(sqrtSeq n)² ≡ x (mod p^(n+1))`. -/
theorem Zp.sqr_sqrtSeq_correct (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp)
            (Zp.sqrtSeq p (Nat.lt_of_succ_lt hp) x sb n)
            (Zp.sqrtSeq p (Nat.lt_of_succ_lt hp) x sb n)).trunc (n + 1)
          = x.trunc (n + 1)
  | 0 => by
    have hp' : 0 < p := Nat.lt_of_succ_lt hp
    rw [Zp.sqr_sqrtSeq_zero_trunc_one p hp' x sb]
    have h_lt : x.trunc 1 < p := by
      show 0 + (x.digits 0).val * p^0 < p
      rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
      exact (x.digits 0).isLt
    exact Nat.mod_eq_of_lt h_lt
  | n + 1 => by
    have hp' : 0 < p := Nat.lt_of_succ_lt hp
    have ih := Zp.sqr_sqrtSeq_correct p hp x sb n
    -- IH transformed: (a*a) % K = xt % K.
    have h_aa_K : ((Zp.sqrtSeq p hp' x sb n).trunc (n + 1)
                    * (Zp.sqrtSeq p hp' x sb n).trunc (n + 1)) % p^(n + 1)
                  = x.trunc (n + 2) % p^(n + 1) := by
      have h1 := ih
      rw [Zp.mul_trunc p hp' _ _ (n + 1)] at h1
      rw [h1, trunc_succ_mod_K p hp' x n]
    -- a % p = sb.d_0 % p.
    have h_a_mod : (Zp.sqrtSeq p hp' x sb n).trunc (n + 1) % p
                  = sb.d_0 % p := by
      rw [trunc_succ_mod_p p hp' (Zp.sqrtSeq p hp' x sb n) n,
          Zp.sqrtSeq_digit_zero p hp' x sb n]
    -- New digit definition reduces to err·two_d_0_inv form.
    have h_d : ((Zp.sqrtSeq p hp' x sb (n + 1)).digits (n + 1)).val
              = Zp.negMod p
                  ((((Zp.sqrtSeq p hp' x sb n).trunc (n + 1)
                    * (Zp.sqrtSeq p hp' x sb n).trunc (n + 1)
                    + (p^(n + 2) - x.trunc (n + 2))) % p^(n + 2)
                    / p^(n + 1)) * sb.two_d_0_inv) := by
      rw [Zp.sqrtSeq_succ_new_digit p hp' x sb n]
      rw [prev_sq_trunc_form p hp' x sb n]
      rw [E213.Meta.Nat.AddMod213.mod_add_mod (Nat.pos_pow_of_pos _ hp')
            ((Zp.sqrtSeq p hp' x sb n).trunc (n + 1)
              * (Zp.sqrtSeq p hp' x sb n).trunc (n + 1))
            (p^(n + 2) - x.trunc (n + 2))]
    -- Apply mul_trunc + succ_trunc_extend, then sqrt_cancel_full.
    rw [Zp.mul_trunc p hp' _ _ (n + 2),
        Zp.sqrtSeq_succ_trunc_extend p hp' x sb n]
    exact sqrt_cancel_full p hp n
      ((Zp.sqrtSeq p hp' x sb n).trunc (n + 1))
      (x.trunc (n + 2))
      sb.d_0
      sb.two_d_0_inv
      (((Zp.sqrtSeq p hp' x sb n).trunc (n + 1)
          * (Zp.sqrtSeq p hp' x sb n).trunc (n + 1)
          + (p^(n + 2) - x.trunc (n + 2))) % p^(n + 2) / p^(n + 1))
      ((Zp.sqrtSeq p hp' x sb (n + 1)).digits (n + 1)).val
      (ZpSeq.trunc_lt_p_pow hp' x (n + 2))
      h_aa_K h_a_mod sb.two_d_0_inv_eq rfl h_d

/-! ## The full square root `sqrtFull`

Diagonal extraction: `sqrtFull.digits k := (sqrtSeq k).digits k`,
collecting the "settled" digit at each position into a single
`ZpSeq`.  This is the true p-adic square root of `x`.
-/

/-- Digit stability: `(sqrtSeq n).digits j = (sqrtSeq j).digits j`
    for `j ≤ n` — higher-level approximations preserve lower digits. -/
theorem Zp.sqrtSeq_digit_stable (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    ∀ n j, j ≤ n →
      (Zp.sqrtSeq p hp x sb n).digits j = (Zp.sqrtSeq p hp x sb j).digits j
  | 0, j, h => by
    have hj : j = 0 := Nat.le_zero.mp h
    rw [hj]
  | n + 1, j, h => by
    cases hcase : Nat.decEq j (n + 1) with
    | isTrue heq => rw [heq]
    | isFalse hne =>
      have hjle_n : j ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h hne)
      rw [Zp.sqrtSeq_succ_digit_below p hp x sb n j hne]
      exact Zp.sqrtSeq_digit_stable p hp x sb n j hjle_n

/-- The full sqrt `ZpSeq p`: extract each "settled" digit. -/
def Zp.sqrtFull (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) : ZpSeq p where
  digits := fun k => (Zp.sqrtSeq p hp x sb k).digits k

/-- `sqrtFull.trunc (n+1) = (sqrtSeq n).trunc (n+1)` — at level n+1,
    sqrtFull's truncation matches the level-n approximation. -/
theorem Zp.sqrtFull_trunc_succ (p : Nat) (hp : 0 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) :
    ∀ n, (Zp.sqrtFull p hp x sb).trunc (n + 1)
          = (Zp.sqrtSeq p hp x sb n).trunc (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih : (Zp.sqrtFull p hp x sb).trunc (n + 1)
              = (Zp.sqrtSeq p hp x sb n).trunc (n + 1) :=
      Zp.sqrtFull_trunc_succ p hp x sb n
    show (Zp.sqrtFull p hp x sb).trunc (n + 1)
          + ((Zp.sqrtFull p hp x sb).digits (n + 1)).val * p^(n + 1)
        = (Zp.sqrtSeq p hp x sb (n + 1)).trunc (n + 1)
          + ((Zp.sqrtSeq p hp x sb (n + 1)).digits (n + 1)).val * p^(n + 1)
    rw [ih]
    rw [← Zp.sqrtSeq_succ_trunc_low p hp x sb n (n + 1) (Nat.le_refl _)]
    rfl

/-- **Full Hensel sqrt correctness**: `sqrtFull² ≡ x (mod p^(n+1))`
    for all `n`. -/
theorem Zp.sqr_sqrtFull_correct (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (sb : Zp.SqrtBase p x) (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp)
      (Zp.sqrtFull p (Nat.lt_of_succ_lt hp) x sb)
      (Zp.sqrtFull p (Nat.lt_of_succ_lt hp) x sb)).trunc (n + 1)
      = x.trunc (n + 1) := by
  rw [Zp.mul_trunc, Zp.sqrtFull_trunc_succ, ← Zp.mul_trunc]
  exact Zp.sqr_sqrtSeq_correct p hp x sb n

/-! ## The 5-adic imaginary unit `i₅ = √(-1) ∈ ℤ_5`

Concrete 5-adic element with `i² = -1`.  Built from
`sqrtBase_neg_one_5` (digit 0 = 2, since `2² = 4 ≡ -1 mod 5`).
-/

/-- The 5-adic square root of -1.  Digit 0 = 2; higher digits
    computed by Hensel iteration. -/
def Zp.i_5 : ZpSeq 5 :=
  Zp.sqrtFull 5 (by decide) (ZpSeq.neg_one 5 (by decide)) Zp.sqrtBase_neg_one_5

/-- Digit 0 of `i₅` is `2`. -/
theorem Zp.i_5_digit_zero : (Zp.i_5.digits 0).val = 2 := rfl

/-- Digit 1 of `i₅` is `1`.  So `i₅ ≡ 2 + 1·5 = 7 (mod 25)`,
    and indeed `7² = 49 ≡ -1 (mod 25)`. -/
theorem Zp.i_5_digit_one : (Zp.i_5.digits 1).val = 1 := by decide

/-- Digit 2 of `i₅` is `2`. -/
theorem Zp.i_5_digit_two : (Zp.i_5.digits 2).val = 2 := by decide

/-- The 13-adic square root of -1.  Digit 0 = 5. -/
def Zp.i_13 : ZpSeq 13 :=
  Zp.sqrtFull 13 (by decide) (ZpSeq.neg_one 13 (by decide))
    Zp.sqrtBase_neg_one_13

/-- Digit 0 of `i₁₃` is `5`. -/
theorem Zp.i_13_digit_zero : (Zp.i_13.digits 0).val = 5 := rfl

/-- Digit 1 of `i₁₃` is `5`.  So `i₁₃ ≡ 5 + 5·13 = 70 (mod 169)`,
    and `70² = 4900 ≡ -1 (mod 169)`. -/
theorem Zp.i_13_digit_one : (Zp.i_13.digits 1).val = 5 := by decide

/-- The 7-adic square root of 2.  Digit 0 = 3. -/
def Zp.sqrt_two_7 : ZpSeq 7 :=
  Zp.sqrtFull 7 (by decide)
    ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩
    Zp.sqrtBase_two_7

/-- Digit 0 of `√2 ∈ ℤ_7` is `3`. -/
theorem Zp.sqrt_two_7_digit_zero : (Zp.sqrt_two_7.digits 0).val = 3 := rfl

/-- Digit 1 of `√2 ∈ ℤ_7` is `1`.  So `√2 ≡ 3 + 1·7 = 10 (mod 49)`,
    and `10² = 100 ≡ 2 (mod 49)`. -/
theorem Zp.sqrt_two_7_digit_one : (Zp.sqrt_two_7.digits 1).val = 1 := by decide

/-- `i₅² ≡ -1 (mod 5)` — the defining property at trunc level 1. -/
theorem Zp.i_5_sq_trunc_one :
    (Zp.mul 5 (by decide) Zp.i_5 Zp.i_5).trunc 1 = 4 := by
  show (Zp.mul 5 (by decide)
          (Zp.sqrtFull 5 (by decide) (ZpSeq.neg_one 5 (by decide))
            Zp.sqrtBase_neg_one_5)
          (Zp.sqrtFull 5 (by decide) (ZpSeq.neg_one 5 (by decide))
            Zp.sqrtBase_neg_one_5)).trunc 1 = 4
  rw [Zp.sqr_sqrtFull_correct 5 (by decide)
        (ZpSeq.neg_one 5 (by decide)) Zp.sqrtBase_neg_one_5 0]
  rfl

/-- `i₅² ≡ -1 (mod 25)` — Hensel correctness lifts to level 2. -/
theorem Zp.i_5_sq_trunc_two :
    (Zp.mul 5 (by decide) Zp.i_5 Zp.i_5).trunc 2
      = (ZpSeq.neg_one 5 (by decide)).trunc 2 := by
  show (Zp.mul 5 (by decide)
          (Zp.sqrtFull 5 (by decide) (ZpSeq.neg_one 5 (by decide))
            Zp.sqrtBase_neg_one_5)
          (Zp.sqrtFull 5 (by decide) (ZpSeq.neg_one 5 (by decide))
            Zp.sqrtBase_neg_one_5)).trunc 2
      = (ZpSeq.neg_one 5 (by decide)).trunc 2
  exact Zp.sqr_sqrtFull_correct 5 (by decide)
    (ZpSeq.neg_one 5 (by decide)) Zp.sqrtBase_neg_one_5 1

end E213.Lib.Math.Padic
