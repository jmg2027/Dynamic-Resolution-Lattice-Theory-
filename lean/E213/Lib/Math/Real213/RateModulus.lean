import E213.Meta.Tactic.NatHelper

/-!
# RateModulus — the general "rate-carrying ⟹ total modulus" theorem

`EulerModulus` gave e a total ∅-axiom cut modulus by carrying the margin invariant
`e_i + 1/(i·d_i) ≤ m/k`.  Nothing in that argument is specific to e once the
**margin-monotone** fact is isolated: if the convergents `a_i/d_i` are increasing and
the margin `e_i + 1/(i·d_i)` is non-increasing (`Htel`), the cut is constant past
`k+2`, uniformly in `(m,k)`.  This file states that abstractly.

`Htel a d` is the *rate certificate* — the cross-multiplied form of "the margin
sequence decreases".  An instance supplies `(a, d)` plus:

  * `hd`     — positive denominators;
  * `htel`   — the margin is non-increasing (the convergence rate);
  * `hmono`  — convergents increasing (gives `false`-forward nesting);
  * `hmonoS` — convergents *strictly* increasing (handles the `m/k = e_{k+1}` edge).

and gets `rate_total_modulus`: a total modulus `N(m,k) = k+2`.  This is the reusable
generator behind `eHolonomicReal` — any real presented by such a rate-carrying
convergent sequence completes unconditionally, with the modulus a constructed value.

Narrative: `theory/math/analysis/holonomic_modulus.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.RateModulus

open E213.Tactic.NatHelper
  (add_mul mul_assoc le_of_mul_le_mul_right add_sub_of_le lt_of_lt_le mul_mul_mul_comm_213)

/-- The convergent cut: `e_i ≤ m/k`, i.e. `a i · k ≤ d i · m`. -/
abbrev rcut (a d : Nat → Nat) (i m k : Nat) : Bool := decide (a i * k ≤ d i * m)

/-- The margin invariant `e_i + 1/(i·d_i) ≤ m/k`, cross-multiplied to `Nat`. -/
abbrev RInv (a d : Nat → Nat) (m k i : Nat) : Prop :=
  (a i * i + 1) * k ≤ m * (i * d i)

/-- The **rate certificate**: the margin `e_i + 1/(i·d_i)` is non-increasing.  Its
    cross-multiplied form, for `i ≥ 1`. -/
def Htel (a d : Nat → Nat) : Prop :=
  ∀ i, 1 ≤ i → (a (i+1)*(i+1)+1)*(i * d i) ≤ (a i * i + 1)*((i+1)*d (i+1))

variable {a d : Nat → Nat}

private theorem swap_kr (P k i : Nat) : (P*k)*i = (P*i)*k := by
  rw [mul_assoc, Nat.mul_comm k i, ← mul_assoc]

private theorem L_base (x k : Nat) : (x*(k+1)+1)*k ≤ (x*k+1)*(k+1) := by
  have l1 : (x*(k+1)+1)*k = x*(k+1)*k + k := by rw [add_mul, Nat.one_mul]
  have l2 : (x*k+1)*(k+1) = x*(k+1)*k + (k+1) := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_assoc, Nat.mul_comm k (k+1), ← mul_assoc]
  rw [l1, l2]; exact Nat.add_le_add_left (Nat.le_succ k) _

private theorem rinv_step (hd : ∀ i, 1 ≤ d i) (htel : Htel a d)
    (m k i : Nat) (hi1 : 1 ≤ i) (ih : RInv a d m k i) : RInv a d m k (i+1) := by
  have hpos : 0 < i * d i := Nat.mul_pos hi1 (hd i)
  have hki : ((a (i+1)*(i+1)+1)*k)*(i*d i) ≤ (m*((i+1)*d (i+1)))*(i*d i) :=
    calc ((a (i+1)*(i+1)+1)*k)*(i*d i)
        = ((a (i+1)*(i+1)+1)*(i*d i))*k := swap_kr _ k (i*d i)
      _ ≤ ((a i*i+1)*((i+1)*d (i+1)))*k := Nat.mul_le_mul_right k (htel i hi1)
      _ = ((a i*i+1)*k)*((i+1)*d (i+1)) := swap_kr _ ((i+1)*d (i+1)) k
      _ ≤ (m*(i*d i))*((i+1)*d (i+1)) := Nat.mul_le_mul_right _ ih
      _ = (m*((i+1)*d (i+1)))*(i*d i) := by
            rw [mul_assoc m (i*d i) ((i+1)*d (i+1)),
                Nat.mul_comm (i*d i) ((i+1)*d (i+1)), ← mul_assoc]
  exact le_of_mul_le_mul_right hpos hki

private theorem rinv (hd : ∀ i, 1 ≤ d i) (htel : Htel a d) (m k : Nat)
    (hstrict : a (k+1) * k + 1 ≤ d (k+1) * m) :
    ∀ i, k + 1 ≤ i → RInv a d m k i := by
  have aux : ∀ t, RInv a d m k (k+1+t) := by
    intro t
    induction t with
    | zero =>
      show (a (k+1)*(k+1)+1)*k ≤ m*((k+1)*d (k+1))
      have e2 : (a (k+1)*k+1)*(k+1) ≤ (d (k+1)*m)*(k+1) :=
        Nat.mul_le_mul_right (k+1) hstrict
      have e3 : (d (k+1)*m)*(k+1) = m*((k+1)*d (k+1)) := by
        rw [Nat.mul_comm (d (k+1)) m, mul_assoc, Nat.mul_comm (d (k+1)) (k+1)]
      exact Nat.le_trans (L_base (a (k+1)) k) (e3 ▸ e2)
    | succ t ih =>
      have hi1 : 1 ≤ k+1+t := Nat.le_trans (Nat.le_add_left 1 k) (Nat.le_add_right (k+1) t)
      exact rinv_step hd htel m k (k+1+t) hi1 ih
  intro i hi; rw [← add_sub_of_le hi]; exact aux (i - (k+1))

private theorem rinv_cut (hd : ∀ i, 1 ≤ d i) (m k i : Nat) (hk : 1 ≤ k)
    (hinv : RInv a d m k i) : rcut a d i m k = true := by
  apply decide_eq_true
  have h1 : (a i*i)*k + k ≤ m*(i*d i) := by
    have e : (a i*i+1)*k = (a i*i)*k + k := by rw [add_mul, Nat.one_mul]
    rw [← e]; exact hinv
  have h2 : (a i*i)*k + 1 ≤ m*(i*d i) := Nat.le_trans (Nat.add_le_add_left hk _) h1
  have el : (a i*i)*k = i*(a i*k) := by rw [Nat.mul_comm (a i) i, mul_assoc]
  have er : m*(i*d i) = i*(m*d i) := by rw [← mul_assoc, Nat.mul_comm m i, mul_assoc]
  rw [el, er] at h2
  have h4 : a i*k < m*d i := by
    rcases Nat.lt_or_ge (a i*k) (m*d i) with h | h
    · exact h
    · exact absurd (lt_of_lt_le h2 (Nat.mul_le_mul_left i h)) (Nat.lt_irrefl _)
  rw [Nat.mul_comm (d i) m]; exact Nat.le_of_lt h4

private theorem false_fwd (hd : ∀ i, 1 ≤ d i)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (m k N : Nat) (hN : rcut a d N m k = false) (i : Nat) (hi : N ≤ i) :
    rcut a d i m k = false := by
  apply decide_eq_false
  have hneg : ¬(a N * k ≤ d N * m) := of_decide_eq_false hN
  have hNlt : d N * m < a N * k := by
    rcases Nat.lt_or_ge (d N * m) (a N * k) with h | h
    · exact h
    · exact absurd h hneg
  intro hle
  have c1 : d N * m * d i < a N * k * d i := Nat.mul_lt_mul_of_pos_right hNlt (hd i)
  have c2 : a N * k * d i ≤ a i * d N * k := by
    calc a N * k * d i = (a N * d i) * k := by
            rw [mul_assoc, Nat.mul_comm k (d i), ← mul_assoc]
      _ ≤ (a i * d N) * k := Nat.mul_le_mul_right k (hmono N i hi)
  have c3 : d N * (m * d i) < d N * (a i * k) := by
    calc d N * (m * d i) = d N * m * d i := (mul_assoc (d N) m (d i)).symm
      _ < a i * d N * k := lt_of_lt_le c1 c2
      _ = d N * (a i * k) := by rw [Nat.mul_comm (a i) (d N), mul_assoc]
  have c4 : m * d i < a i * k := by
    rcases Nat.lt_or_ge (m * d i) (a i * k) with h | h
    · exact h
    · exact absurd (lt_of_lt_le c3 (Nat.mul_le_mul_left (d N) h)) (Nat.lt_irrefl _)
  rw [Nat.mul_comm (d i) m] at hle
  exact absurd hle (Nat.not_le.mpr c4)

private theorem eq_false (m k : Nat) (hk : 1 ≤ k)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (heq : a (k+1) * k = d (k+1) * m) : rcut a d (k+2) m k = false := by
  apply decide_eq_false
  intro hle
  have key : d (k+1) * (m * d (k+2)) < d (k+1) * (a (k+2) * k) := by
    calc d (k+1) * (m * d (k+2))
        = a (k+1) * k * d (k+2) := by rw [← mul_assoc, ← heq]
      _ = a (k+1) * d (k+2) * k := by rw [mul_assoc, Nat.mul_comm k (d (k+2)), ← mul_assoc]
      _ < a (k+2) * d (k+1) * k := Nat.mul_lt_mul_of_pos_right (hmonoS (k+1)) hk
      _ = d (k+1) * (a (k+2) * k) := by rw [Nat.mul_comm (a (k+2)) (d (k+1)), mul_assoc]
  have c : m * d (k+2) < a (k+2) * k := by
    rcases Nat.lt_or_ge (m * d (k+2)) (a (k+2) * k) with h | h
    · exact h
    · exact absurd (lt_of_lt_le key (Nat.mul_le_mul_left (d (k+1)) h)) (Nat.lt_irrefl _)
  rw [Nat.mul_comm (d (k+2)) m] at hle
  exact absurd hle (Nat.not_le.mpr c)

/-- ★★★ **Abstract rate-carrying ⟹ total modulus (constant form).**  A monotone
    convergent cut-sequence `a_i/d_i` with a non-increasing margin `e_i + 1/(i·d_i)`
    (`Htel`) has its cut constant past `k+2`: `rcut a d i m k = rcut a d j m k` for
    all `i, j ≥ k+2` (`k ≥ 1`).  No LEM, no irrationality measure — the rate
    certificate alone suffices. -/
theorem rate_cut_const (hd : ∀ i, 1 ≤ d i) (htel : Htel a d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) (i j : Nat) (hi : k+2 ≤ i) (hj : k+2 ≤ j) :
    rcut a d i m k = rcut a d j m k := by
  have hk1i : k+1 ≤ i := Nat.le_trans (Nat.le_succ _) hi
  have hk1j : k+1 ≤ j := Nat.le_trans (Nat.le_succ _) hj
  rcases Nat.lt_trichotomy (a (k+1)*k) (d (k+1)*m) with hlt | heq | hgt
  · exact (rinv_cut hd m k i hk (rinv hd htel m k hlt i hk1i)).trans
        (rinv_cut hd m k j hk (rinv hd htel m k hlt j hk1j)).symm
  · have hf := eq_false m k hk hmonoS heq
    exact (false_fwd hd hmono m k (k+2) hf i hi).trans
        (false_fwd hd hmono m k (k+2) hf j hj).symm
  · have hfalse : rcut a d (k+1) m k = false := decide_eq_false (Nat.not_le.mpr hgt)
    exact (false_fwd hd hmono m k (k+1) hfalse i hk1i).trans
        (false_fwd hd hmono m k (k+1) hfalse j hk1j).symm

/-- ★★★ **The general generator, existential form.**  Every rate-carrying convergent
    cut-sequence has a total ∅-axiom modulus (`N = k+2`). -/
theorem rate_total_modulus (hd : ∀ i, 1 ≤ d i) (htel : Htel a d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  ⟨k+2, fun i j hi hj => rate_cut_const hd htel hmono hmonoS m k hk i j hi hj⟩

/-- ★★★ **The depth-rank ⟶ rate-certificate bridge.**  The rate certificate `Htel`
    is exactly a *smallness* condition on the **cross-determinant** `W_i = a_{i+1}·d_i
    − a_i·d_{i+1}` (the divergence-ladder's central object, here given by `hW`): the
    margin is non-increasing iff `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`, i.e. the
    cross-det is small relative to the denominator's discrete growth.  This is where
    the depth arc (cross-determinant `W`) meets the modulus generator (rate `Htel`):
    a real whose cross-determinant is controlled by its denominator growth carries its
    own modulus. -/
theorem Htel_of_crossdet (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i)
    (hcond : ∀ i, 1 ≤ i → i*(i+1)*W i + i*d i ≤ (i+1)*d (i+1)) : Htel a d := by
  intro i hi
  show (a (i+1)*(i+1)+1)*(i*d i) ≤ (a i*i+1)*((i+1)*d (i+1))
  have hLHS : (a (i+1)*(i+1)+1)*(i*d i) = i*(i+1)*(a (i+1)*d i) + i*d i := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a (i+1)) i, ← mul_mul_mul_comm_213]
  have hRHS : (a i*i+1)*((i+1)*d (i+1)) = i*(i+1)*(a i*d (i+1)) + (i+1)*d (i+1) := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a i) (i+1), mul_mul_mul_comm_213,
        Nat.mul_comm (i+1) i]
  rw [hLHS, hRHS, hW i, Nat.mul_add, Nat.add_assoc]
  exact Nat.add_le_add_left (hcond i hi) _

end E213.Lib.Math.Real213.RateModulus
