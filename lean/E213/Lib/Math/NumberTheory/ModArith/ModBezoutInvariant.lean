import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChoosePrime
import E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole
/-!
# Bezout invariant proof — universal correctness of xgcd

Single-step invariant: one application of the xgcd recursion preserves
the modular Bezout invariant.  Once established, induction on fuel
gives the universal correctness of `xgcdAux` and `modBezout`.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ModBezoutInvariant

open E213.Lib.Math.NumberTheory.ModArith.ModBezout (bezoutSubMod xgcdAux modBezout)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self div_add_mod
                              mod_diff_eq_zero_of_le)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_mul add_sub_cancel_right sub_add_cancel)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChoosePrime (mul_p_mod_eq_zero)

/-! ## PURE Nat replacements -/

/-- `(B + Z) - (A + Z) = B - A`.  PURE replacement for
    `Nat.add_sub_add_right` (propext-dirty).  By induction on Z. -/
theorem add_sub_add_right_pure : ∀ (B Z A : Nat), (B + Z) - (A + Z) = B - A
  | B, 0, A => by rw [Nat.add_zero, Nat.add_zero]
  | B, k + 1, A => by
    show (B + (k + 1)) - (A + (k + 1)) = B - A
    rw [show B + (k + 1) = (B + k) + 1 from (Nat.add_assoc B k 1).symm,
        show A + (k + 1) = (A + k) + 1 from (Nat.add_assoc A k 1).symm,
        Nat.succ_sub_succ_eq_sub (B + k) (A + k)]
    exact add_sub_add_right_pure B k A

/-! ## Mod-p cancellation -/

/-- **Mod-p cancellation**: `A, B < p ∧ (A + Z) % p = (B + Z) % p ⟹ A = B`. -/
theorem mod_cancel_right (p A B Z : Nat) (hp : 0 < p)
    (hA : A < p) (hB : B < p)
    (h : (A + Z) % p = (B + Z) % p) : A = B := by
  rcases Nat.le_total A B with hAB | hBA
  · have h_le : A + Z ≤ B + Z := Nat.add_le_add_right hAB Z
    have h_diff : ((B + Z) - (A + Z)) % p = 0 :=
      mod_diff_eq_zero_of_le hp h_le h
    rw [add_sub_add_right_pure B Z A] at h_diff
    have h_lt : B - A < p := Nat.lt_of_le_of_lt (Nat.sub_le B A) hB
    rw [Nat.mod_eq_of_lt h_lt] at h_diff
    exact Nat.le_antisymm hAB (Nat.le_of_sub_eq_zero h_diff)
  · have h_le : B + Z ≤ A + Z := Nat.add_le_add_right hBA Z
    have h_diff : ((A + Z) - (B + Z)) % p = 0 :=
      mod_diff_eq_zero_of_le hp h_le h.symm
    rw [add_sub_add_right_pure A Z B] at h_diff
    have h_lt : A - B < p := Nat.lt_of_le_of_lt (Nat.sub_le A B) hA
    rw [Nat.mod_eq_of_lt h_lt] at h_diff
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero h_diff) hBA

/-! ## Algebraic sub-lemmas for the step invariant -/

/-- `((a · x₂) % p + (a · q · x₁) % p) % p = (a · x₀) % p`
    where `x₂ = bezoutSubMod p q x₀ x₁`.

    Derivation: `a · (x₀ + (p - r)) + a · r = a · x₀ + a · p ≡ a · x₀ mod p`. -/
private theorem aux_lhs_eq (p a q x₀ x₁ : Nat) (hp : 0 < p) :
    ((a * bezoutSubMod p q x₀ x₁) % p + (a * q * x₁) % p) % p
      = (a * x₀) % p := by
  let r := (q * x₁) % p
  have hr_lt : r < p := Nat.mod_lt _ hp
  have hr_le : r ≤ p := Nat.le_of_lt hr_lt
  -- (a * bezoutSubMod) % p = (a * (x₀ + (p - r))) % p = (a*x₀ + a*(p - r)) % p
  have h_step1 : (a * bezoutSubMod p q x₀ x₁) % p
               = (a * x₀ + a * (p - r)) % p := by
    show (a * ((x₀ + (p - r)) % p)) % p = (a * x₀ + a * (p - r)) % p
    rw [← mul_mod_right_pure a (x₀ + (p - r)) p, Nat.mul_add]
  -- ((a*x₀ + a*(p - r)) + a*r) = a*x₀ + a*p
  have h_combine : (a * x₀ + a * (p - r)) + a * r = a * x₀ + a * p := by
    rw [Nat.add_assoc (a * x₀) (a * (p - r)) (a * r)]
    rw [← Nat.mul_add a (p - r) r]
    rw [show (p - r) + r = p from sub_add_cancel hr_le]
  -- ((a*x₀ + a*(p - r)) + a*r) % p = (a*x₀ + a*p) % p = (a*x₀) % p
  have h_modded : ((a * x₀ + a * (p - r)) + a * r) % p = (a * x₀) % p := by
    rw [h_combine, add_mod_gen (a * x₀) (a * p) p,
        Nat.mul_comm a p, mul_p_mod_eq_zero p a, Nat.add_zero, mod_mod]
  -- ((a*x₀ + a*(p - r)) % p + (a*r) % p) % p = (a*x₀) % p
  have h_split : ((a * x₀ + a * (p - r)) % p + (a * r) % p) % p = (a * x₀) % p := by
    rw [← add_mod_gen (a * x₀ + a * (p - r)) (a * r) p]
    exact h_modded
  -- (a*r) % p = (a * q * x₁) % p (since r = (q*x₁) % p)
  have h_ar : (a * r) % p = (a * q * x₁) % p := by
    show (a * ((q * x₁) % p)) % p = (a * q * x₁) % p
    rw [← mul_mod_right_pure a (q * x₁) p, ← mul_assoc a q x₁]
  rw [h_ar] at h_split
  rw [← h_step1] at h_split
  exact h_split

/-- `(r₂ % p + (a · q · x₁) % p) % p = (a · x₀) % p`
    where `r₂ = r₀ % r₁`, `q = r₀ / r₁`, given the inductive hypotheses. -/
private theorem aux_rhs_eq (p a r₀ r₁ x₀ x₁ : Nat)
    (h₀ : r₀ % p = (a * x₀) % p)
    (h₁ : r₁ % p = (a * x₁) % p) :
    ((r₀ % r₁) % p + (a * (r₀ / r₁) * x₁) % p) % p = (a * x₀) % p := by
  -- r₀ = r₁ * (r₀/r₁) + r₀ % r₁  (div_add_mod)
  have h_dam : r₁ * (r₀ / r₁) + r₀ % r₁ = r₀ := div_add_mod r₀ r₁
  -- r₀ % p = (r₁ * (r₀/r₁) + r₀ % r₁) % p
  have h_modr₀ : r₀ % p = (r₁ * (r₀ / r₁) + r₀ % r₁) % p := by rw [h_dam]
  -- Combine with h₀
  have h_mod_combined : (r₁ * (r₀ / r₁) + r₀ % r₁) % p = (a * x₀) % p :=
    h_modr₀.symm.trans h₀
  -- Split via add_mod_gen
  rw [add_mod_gen (r₁ * (r₀ / r₁)) (r₀ % r₁) p] at h_mod_combined
  -- ((r₁ * q) % p + (r₀ % r₁) % p) % p = (a * x₀) % p
  -- Reduce (r₁ * q) % p = (a * q * x₁) % p
  have h_r1q : (r₁ * (r₀ / r₁)) % p = (a * (r₀ / r₁) * x₁) % p := by
    rw [mul_mod_left_pure r₁ (r₀ / r₁) p, h₁]
    rw [← mul_mod_left_pure (a * x₁) (r₀ / r₁) p]
    -- (a*x₁ * q) % p = (a * q * x₁) % p
    rw [Nat.mul_comm a x₁, Nat.mul_comm (x₁ * a) (r₀ / r₁)]
    rw [← mul_assoc (r₀ / r₁) x₁ a]
    rw [Nat.mul_comm (r₀ / r₁ * x₁) a, mul_assoc a (r₀ / r₁) x₁]
  rw [h_r1q] at h_mod_combined
  -- ((a * q * x₁) % p + (r₀ % r₁) % p) % p = (a * x₀) % p
  -- Reorder via Nat.add_comm: ((r₀ % r₁) % p + (a*q*x₁) % p) % p = (a * x₀) % p
  rw [Nat.add_comm ((a * (r₀ / r₁) * x₁) % p) ((r₀ % r₁) % p)] at h_mod_combined
  exact h_mod_combined

/-- ★★★ **Single-step Bezout invariant**:

    Given the modular invariants for `(r₀, x₀)` and `(r₁, x₁)`, one xgcd
    step preserves the invariant:

      `(r₀ % r₁) % p = (a · bezoutSubMod p (r₀/r₁) x₀ x₁) % p`.

    PURE.  Combines `aux_lhs_eq` + `aux_rhs_eq` + `mod_cancel_right`. -/
theorem step_invariant (p a r₀ r₁ x₀ x₁ : Nat) (hp : 0 < p)
    (h₀ : r₀ % p = (a * x₀) % p)
    (h₁ : r₁ % p = (a * x₁) % p) :
    (r₀ % r₁) % p
      = (a * bezoutSubMod p (r₀ / r₁) x₀ x₁) % p := by
  have h_lhs := aux_lhs_eq p a (r₀ / r₁) x₀ x₁ hp
  have h_rhs := aux_rhs_eq p a r₀ r₁ x₀ x₁ h₀ h₁
  -- h_lhs : ((a * x₂) % p + (a*q*x₁) % p) % p = (a*x₀) % p
  -- h_rhs : ((r₂) % p + (a*q*x₁) % p) % p = (a*x₀) % p (with r₂ = r₀ % r₁)
  -- So ((a*x₂) % p + Z) % p = (r₂ % p + Z) % p  with Z = (a*q*x₁) % p
  -- By mod_cancel_right: (a*x₂) % p = r₂ % p
  have h_eq : ((a * bezoutSubMod p (r₀ / r₁) x₀ x₁) % p
               + (a * (r₀ / r₁) * x₁) % p) % p
            = ((r₀ % r₁) % p + (a * (r₀ / r₁) * x₁) % p) % p :=
    h_lhs.trans h_rhs.symm
  have h_A_lt : (a * bezoutSubMod p (r₀ / r₁) x₀ x₁) % p < p := Nat.mod_lt _ hp
  have h_B_lt : (r₀ % r₁) % p < p := Nat.mod_lt _ hp
  exact (mod_cancel_right p (a * bezoutSubMod p (r₀ / r₁) x₀ x₁ % p)
    ((r₀ % r₁) % p) ((a * (r₀ / r₁) * x₁) % p) hp
    h_A_lt h_B_lt h_eq).symm

/-! ## Inductive correctness of xgcdAux -/

/-- ★★★★ **xgcdAux invariant preservation** (induction on fuel):

    For any fuel, initial state `(r₀, r₁, x₀, x₁)` satisfying the modular
    Bezout invariants, the output `(g, x) := xgcdAux p fuel ...` also
    satisfies `g % p = (a · x) % p`.

    PURE.  Base cases (fuel = 0 or r₁ = 0): output is `(r₀, x₀)`, invariant
    matches hypothesis.  Step case: apply `step_invariant` + IH. -/
theorem xgcdAux_invariant (p a : Nat) (hp : 0 < p) :
    ∀ (fuel r₀ r₁ x₀ x₁ : Nat),
      r₀ % p = (a * x₀) % p →
      r₁ % p = (a * x₁) % p →
      (xgcdAux p fuel r₀ r₁ x₀ x₁).1 % p
        = (a * (xgcdAux p fuel r₀ r₁ x₀ x₁).2) % p
  | 0,      r₀, _,     x₀, _,  h₀, _  => by
    show r₀ % p = (a * x₀) % p
    exact h₀
  | _ + 1,  r₀, 0,     x₀, _,  h₀, _  => by
    show r₀ % p = (a * x₀) % p
    exact h₀
  | f + 1,  r₀, n + 1, x₀, x₁, h₀, h₁ => by
    -- Recursive case: xgcdAux p (f+1) r₀ (n+1) x₀ x₁
    --   = xgcdAux p f (n+1) (r₀ % (n+1)) x₁ (bezoutSubMod p (r₀/(n+1)) x₀ x₁)
    have h_step : (r₀ % (n + 1)) % p
                 = (a * bezoutSubMod p (r₀ / (n + 1)) x₀ x₁) % p :=
      step_invariant p a r₀ (n + 1) x₀ x₁ hp h₀ h₁
    show (xgcdAux p f (n + 1) (r₀ % (n + 1)) x₁
            (bezoutSubMod p (r₀ / (n + 1)) x₀ x₁)).1 % p
       = (a * (xgcdAux p f (n + 1) (r₀ % (n + 1)) x₁
                (bezoutSubMod p (r₀ / (n + 1)) x₀ x₁)).2) % p
    exact xgcdAux_invariant p a hp f (n + 1) (r₀ % (n + 1)) x₁
      (bezoutSubMod p (r₀ / (n + 1)) x₀ x₁) h₁ h_step

/-! ## Specialization: `modBezout` invariant -/

/-- ★★★★★ **modBezout invariant** (universal):

    For any `0 < p`, `(modBezout a p).1 % p = (a · (modBezout a p).2) % p`.

    Apply `xgcdAux_invariant` at the initial state `(a, p, 1, 0)`,
    which satisfies the invariants trivially:
      · `a % p = (a · 1) % p`  (since `a · 1 = a`)
      · `p % p = 0 = (a · 0) % p`  (since `a · 0 = 0`)

    PURE.  This is the universal Bezout correctness theorem. -/
theorem modBezout_invariant (a p : Nat) (hp : 0 < p) :
    (modBezout a p).1 % p = (a * (modBezout a p).2) % p := by
  -- modBezout a p = xgcdAux p (a + p + 1) a p 1 0
  show (xgcdAux p (a + p + 1) a p 1 0).1 % p
     = (a * (xgcdAux p (a + p + 1) a p 1 0).2) % p
  apply xgcdAux_invariant p a hp
  · -- a % p = (a * 1) % p
    rw [Nat.mul_one]
  · -- p % p = (a * 0) % p
    rw [Nat.mul_zero, mod_self]
    rfl

/-! ## Universal modular inverse from coprimality

When `(modBezout a p).1 = 1` (i.e., `gcd(a, p) = 1`, which is the
algorithm's output when its first component equals 1), the second
component is the modular inverse:

  `(a · (modBezout a p).2) % p = 1 % p`. -/

/-- ★★★★★★ **Universal modular inverse**:

    Given `0 < p` and `(modBezout a p).1 = 1`, the second component
    of `modBezout a p` is the modular inverse of `a` mod `p`:

      `(a · (modBezout a p).2) % p = 1 % p`.

    PURE.  Direct consequence of `modBezout_invariant`. -/
theorem modBezout_inverse_correct (a p : Nat) (hp : 0 < p)
    (h_gcd_one : (modBezout a p).1 = 1) :
    (a * (modBezout a p).2) % p = 1 % p := by
  have h := modBezout_invariant a p hp
  rw [h_gcd_one] at h
  exact h.symm

/-! ## Smoke verifications of universal correctness -/

/-- Smoke at (2, 5): the abstract `modBezout_inverse_correct`
    matches the per-prime decide. -/
theorem smoke_2_5 : (2 * (modBezout 2 5).2) % 5 = 1 % 5 :=
  modBezout_inverse_correct 2 5 (by decide) (by decide)

theorem smoke_3_7 : (3 * (modBezout 3 7).2) % 7 = 1 % 7 :=
  modBezout_inverse_correct 3 7 (by decide) (by decide)

theorem smoke_4_11 : (4 * (modBezout 4 11).2) % 11 = 1 % 11 :=
  modBezout_inverse_correct 4 11 (by decide) (by decide)

theorem smoke_9_19 : (9 * (modBezout 9 19).2) % 19 = 1 % 19 :=
  modBezout_inverse_correct 9 19 (by decide) (by decide)

/-! ## Universal `ModInverse` constructor from Bezout

This is the payoff: given any `(a, p)` with `gcd(a, p) = 1` (witnessed
by `(modBezout a p).1 = 1`), we construct a universal `ModInverse p a`
without any per-prime hypothesis.  Bezout coefficient `(modBezout a p).2`
mod p gives the inverse.
-/

open E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole (ModInverse)

/-- ★★★★★★★ **Universal ModInverse from Bezout**:

    For `0 < p` and `(modBezout a p).1 = 1` (gcd-1 witness),
    `modInverseFromBezout a p hp h` is a `ModInverse p a` with
    `inv := (modBezout a p).2 % p`.

    PURE.  No per-prime hypothesis needed.  This unlocks universal
    FLT applications + Phase 3.2 universal closure (subject to
    universal middle-binomial vanishing). -/
def modInverseFromBezout (a p : Nat) (hp : 0 < p)
    (h_gcd : (modBezout a p).1 = 1) : ModInverse p a where
  inv := (modBezout a p).2 % p
  inv_lt := Nat.mod_lt _ hp
  inv_eq := by
    show (a * ((modBezout a p).2 % p)) % p = 1 % p
    rw [← mul_mod_right_pure a (modBezout a p).2 p]
    exact modBezout_inverse_correct a p hp h_gcd

/-! ## Universal smoke applications -/

/-- Smoke: universal ModInverse for (2, 5) via Bezout.
    The `inv_eq` field is the universal `modBezout_inverse_correct`,
    not a per-prime `decide`. -/
def modInverse_2_5_universal : ModInverse 5 2 :=
  modInverseFromBezout 2 5 (by decide) (by decide)

def modInverse_3_7_universal : ModInverse 7 3 :=
  modInverseFromBezout 3 7 (by decide) (by decide)

def modInverse_4_11_universal : ModInverse 11 4 :=
  modInverseFromBezout 4 11 (by decide) (by decide)

def modInverse_9_19_universal : ModInverse 19 9 :=
  modInverseFromBezout 9 19 (by decide) (by decide)

end E213.Lib.Math.NumberTheory.ModArith.ModBezoutInvariant
