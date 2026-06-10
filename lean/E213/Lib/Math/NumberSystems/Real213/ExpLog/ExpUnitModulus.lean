import E213.Lib.Math.NumberSystems.Real213.RateModulus
import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.Analysis.Cauchy.Euler
import E213.Meta.Nat.PolyNatMTactic

/-!
# ExpUnitModulus — `exp(1/q)` has a TOTAL constructive cut modulus, for every `q ≥ 1`

The `expCauchySeq` marathon (frontier: `ricci_flow_smooth_core.md`).  The euler
generator (`RateModulus.rate_total_modulus`, instantiated for `e = exp(1)` in
`EulerModulus`) extends **verbatim** to the whole unit-fraction exponential family:

  `exp(1/q) = Σ_k (1/q)ᵏ/k!`,  convergents `a_n/d_n` with `d_n = qⁿ·n!`,

via the recurrences `a_{n+1} = (n+1)·q·a_n + 1`, `d_{n+1} = (n+1)·q·d_n` (`a_0 = d_0
= 1`).  The cross-determinant is *exactly the denominator* — `a_{i+1}·d_i = a_i·d_{i+1}
+ d_i` (`expU_cross_det`), same as e — and the `Htel` side condition reduces to

  `i(i+1) + i ≤ (i+1)²·q`,

which holds for **every** `q ≥ 1` (it is `i²+2i ≤ i²+2i+1` at `q = 1`, and only
improves with `q`).  So each `exp(1/q)` is a genuine `CauchyCutSeq` with the total
∅-axiom modulus `N(m,k) = k+2` (`expUnitCauchySeq`), uniformly in `q`: a parametric
family of completed-line points — `e` (`q = 1`, agreeing with `eulerNum/eulerDen`
definitionally: `expU_one_num/den`), `√e = exp(1/2)` (`q = 2`, `sqrtECauchySeq`), ….

**Honest boundary**: general `exp(p/q)` (`p ≥ 2`) does *not* fit this generator — the
early Taylor increments exceed the `1/i`-margin envelope `Htel` encodes, so the
modulus must be offset past a `p/q`-dependent burn-in (the `CutExpModulus` ratio-test
threshold `2M ≤ k+1`).  That offset generalization of `RateModulus`, or the
multiplicative route `exp(p/q) = exp(1/q)ᵖ` through cut multiplication, is the
remaining T2 step — recorded, not claimed.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen)
open E213.Lib.Math.NumberSystems.Real213.RateModulus
  (rcut Htel Htel_of_crossdet rate_cut_const)

/-! ## §1 — the convergents of `exp(1/q)` -/

/-- Numerator of the `n`-th partial sum of `exp(1/q)` over the denominator `qⁿ·n!`:
    `a_{n+1} = (n+1)·q·a_n + 1` (`a_n/d_n = Σ_{k≤n} (1/q)ᵏ/k!`). -/
def expUNum (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * q * expUNum q n + 1

/-- Denominator `d_n = qⁿ·n!`, by the recurrence `d_{n+1} = (n+1)·q·d_n`. -/
def expUDen (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * q * expUDen q n

/-- Denominators are positive (`q ≥ 1`). -/
theorem expUDen_pos (q : Nat) (hq : 1 ≤ q) : ∀ i, 1 ≤ expUDen q i
  | 0 => Nat.le_refl 1
  | i + 1 =>
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le i)) hq)
      (expUDen_pos q hq i)

/-- ★★ **The cross-determinant is exactly the denominator** (the e-pattern, uniform in
    `q`): `a_{i+1}·d_i = a_i·d_{i+1} + d_i`.  The increment of the partial sum is one
    unit of the next resolution — the divergence-form identity that feeds `Htel`. -/
theorem expU_cross_det (q i : Nat) :
    expUNum q (i + 1) * expUDen q i
      = expUNum q i * expUDen q (i + 1) + expUDen q i := by
  show ((i + 1) * q * expUNum q i + 1) * expUDen q i
      = expUNum q i * ((i + 1) * q * expUDen q i) + expUDen q i
  ring_nat

/-! ## §2 — the convergents increase -/

/-- Strict increase (cross-multiplied): the difference is exactly `d_i > 0`. -/
theorem expU_hmonoS (q : Nat) (hq : 1 ≤ q) (i : Nat) :
    expUNum q i * expUDen q (i + 1) < expUNum q (i + 1) * expUDen q i := by
  rw [expU_cross_det q i]
  exact Nat.lt_add_of_pos_right (expUDen_pos q hq i)

/-- Increase across any gap (iterated, cross-multiplied). -/
theorem expU_hmono (q N : Nat) :
    ∀ i, N ≤ i → expUNum q N * expUDen q i ≤ expUNum q i * expUDen q N := by
  have aux : ∀ t, expUNum q N * expUDen q (N + t)
      ≤ expUNum q (N + t) * expUDen q N := by
    intro t
    induction t with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      show expUNum q N * ((N + t + 1) * q * expUDen q (N + t))
          ≤ ((N + t + 1) * q * expUNum q (N + t) + 1) * expUDen q N
      rw [show expUNum q N * ((N + t + 1) * q * expUDen q (N + t))
            = (N + t + 1) * q * (expUNum q N * expUDen q (N + t)) from by ring_nat]
      refine Nat.le_trans (Nat.mul_le_mul_left ((N + t + 1) * q) ih) ?_
      rw [show (N + t + 1) * q * (expUNum q (N + t) * expUDen q N)
            = ((N + t + 1) * q * expUNum q (N + t)) * expUDen q N from by ring_nat]
      exact Nat.mul_le_mul (Nat.le_add_right _ 1) (Nat.le_refl _)
  intro i hi
  obtain ⟨t, ht⟩ := Nat.le.dest hi
  rw [← ht]
  exact aux t

/-! ## §3 — the rate certificate, uniform in `q` -/

/-- ★★★ **`exp(1/q)` satisfies the rate certificate `Htel`, for every `q ≥ 1`.**  Via
    `Htel_of_crossdet` with `W = expUDen q`; the side condition reduces to
    `i(i+1) + i ≤ (i+1)²·q` — at `q = 1` it is `i²+2i ≤ i²+2i+1`, and the right side
    only grows with `q`.  The unit-fraction family rides the e-certificate uniformly. -/
theorem expU_Htel (q : Nat) (hq : 1 ≤ q) : Htel (expUNum q) (expUDen q) :=
  Htel_of_crossdet (expUDen q) (fun i => expU_cross_det q i) (fun i _ => by
    show i * (i + 1) * expUDen q i + i * expUDen q i
        ≤ (i + 1) * expUDen q (i + 1)
    rw [show (i + 1) * expUDen q (i + 1) = ((i + 1) * (i + 1) * q) * expUDen q i from by
          show (i + 1) * ((i + 1) * q * expUDen q i)
              = ((i + 1) * (i + 1) * q) * expUDen q i
          ring_nat,
        show i * (i + 1) * expUDen q i + i * expUDen q i
            = (i * (i + 1) + i) * expUDen q i from by ring_nat]
    refine Nat.mul_le_mul_right (expUDen q i) ?_
    have h1 : i * (i + 1) + i ≤ (i + 1) * (i + 1) := by
      rw [show (i + 1) * (i + 1) = i * (i + 1) + i + 1 from by ring_nat]
      exact Nat.le_succ _
    refine Nat.le_trans h1 ?_
    have h2 := Nat.mul_le_mul_left ((i + 1) * (i + 1)) hq
    rwa [Nat.mul_one] at h2)

/-! ## §4 — the total modulus + the `CauchyCutSeq` family -/

/-- The cut of `exp(1/q)` reads `true` at every `k = 0` test-point (the whole line
    below any resolution-`0` probe). -/
theorem expU_cut_at_zero (q i m : Nat) :
    rcut (expUNum q) (expUDen q) i m 0 = true := by
  apply decide_eq_true
  exact Nat.le_trans (Nat.le_of_eq (Nat.mul_zero _)) (Nat.zero_le _)

/-- ★★★ **`exp(1/q)`'s cut is constant past `k+2`, for every `q ≥ 1`** — the total
    ∅-axiom modulus `N(m,k) = k+2`, uniform in `(m,k)` *and in `q`*.  Direct instance
    of the general generator `rate_cut_const`. -/
theorem expUnit_cut_const (q : Nat) (hq : 1 ≤ q) (m k : Nat) (hk : 1 ≤ k) (i j : Nat)
    (hi : k + 2 ≤ i) (hj : k + 2 ≤ j) :
    rcut (expUNum q) (expUDen q) i m k = rcut (expUNum q) (expUDen q) j m k :=
  rate_cut_const (expUDen_pos q hq) (expU_Htel q hq) (expU_hmono q) (expU_hmonoS q hq)
    m k hk i j hi hj

/-- ★★★★★ **The `exp(1/q)` family as `Real213` Cauchy points.**  For every `q ≥ 1`,
    the convergent cut-sequence of `exp(1/q)` is a genuine `CauchyCutSeq` with the
    constructed total modulus `N(m,k) = k+2` — the unit-fraction exponentials inhabit
    the completed line unconditionally, the same constructive footing as `e`
    (`eulerCauchySeq`, the `q = 1` member).  This discharges the `expCauchySeq`
    frontier brick for the whole unit-fraction family at once. -/
def expUnitCauchySeq (q : Nat) (hq : 1 ≤ q) : CauchyCutSeq where
  cs := fun i => rcut (expUNum q) (expUDen q) i
  N := fun _ k => k + 2
  cauchy := by
    intro m k i j hi hj
    cases k with
    | zero =>
      show rcut (expUNum q) (expUDen q) i m 0 = rcut (expUNum q) (expUDen q) j m 0
      rw [expU_cut_at_zero q i m, expU_cut_at_zero q j m]
    | succ k' =>
      exact expUnit_cut_const q hq m (k' + 1) (Nat.succ_le_succ (Nat.zero_le k'))
        i j hi hj

/-- The extracted limit is the stable convergent value: for `k ≥ 1` and any
    `i ≥ k+2`, the limit cut at `(m,k)` equals `rcut … i m k`. -/
theorem expUnitCauchySeq_cut_stable (q : Nat) (hq : 1 ≤ q) (m k : Nat) (hk : 1 ≤ k)
    (i : Nat) (hi : k + 2 ≤ i) :
    (expUnitCauchySeq q hq).limit m k = rcut (expUNum q) (expUDen q) i m k := by
  show rcut (expUNum q) (expUDen q) (k + 2) m k = rcut (expUNum q) (expUDen q) i m k
  exact expUnit_cut_const q hq m k hk (k + 2) i (Nat.le_refl _) hi

/-- ★★ **`√e` is a `Real213` Cauchy point**: the `q = 2` member, `exp(1/2)`. -/
def sqrtECauchySeq : CauchyCutSeq := expUnitCauchySeq 2 (by decide)

/-! ## §5 — sanity: the `q = 1` member IS e's convergent sequence -/

/-- `expUNum 1 = eulerNum` (definitional induction: the recurrences coincide). -/
theorem expU_one_num : ∀ n, expUNum 1 n = eulerNum n
  | 0 => rfl
  | n + 1 => by
    show (n + 1) * 1 * expUNum 1 n + 1 = (n + 1) * eulerNum n + 1
    rw [expU_one_num n, Nat.mul_one]

/-- `expUDen 1 = eulerDen`. -/
theorem expU_one_den : ∀ n, expUDen 1 n = eulerDen n
  | 0 => rfl
  | n + 1 => by
    show (n + 1) * 1 * expUDen 1 n = (n + 1) * eulerDen n
    rw [expU_one_den n, Nat.mul_one]

end E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus
