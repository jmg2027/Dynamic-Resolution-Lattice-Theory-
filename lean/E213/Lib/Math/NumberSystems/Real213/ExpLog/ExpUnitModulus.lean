import E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus
import E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.Analysis.Cauchy.Euler
import E213.Meta.Nat.NatRing213
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

**Honest boundary**: general `exp(p/q)` (`p ≥ 2`) does *not* fit this generator — and
§6 **proves** it (the ζ(3)-overtake mirror, `RateStratification`): the factorial
presentation's cross-determinant `p^{i+1}·dᵢ` overtakes the denominator quantum at
layer `q+9` (`exp_pq_presentation_overtakes`), so by `htel_iff_dominates` **no `Htel`
certificate exists for it** (`exp_pq_no_htel`) — rate is a property of the pointing,
not the real.  The completion of `exp(p/q)` therefore needs a different *presentation*
(dyadic brackets on the `CutExpModulus` tail bound, the `CubeRootTwoCut` schedule
pattern) or a graded margin (`modulus_degree_ladder.md`, rung 1) — recorded, not
claimed.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus
open E213.Lib.Math.NumberSystems.Real213.Modulus

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus
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

/-! ## §6 — the `p ≥ 2` boundary: the factorial presentation is rate-free (proven)

The ζ(3) mirror (`Zeta3Cut.zeta3_presentation_overtakes`): for `exp(p/q)` with
`p ≥ 2`, the factorial-cleared presentation `expNum p q / expUDen q` has
cross-determinant `p^{i+1}·dᵢ`, which **overtakes** the denominator quantum
`(i+1)·d_{i+1} = (i+1)²q·dᵢ` as soon as `(i+1)²q < p^{i+1}` — witnessed at layer
`i = q+9` via `(q+10)²q < (q+10)³ < 2^{q+10} ≤ p^{q+10}`.  By
`RateStratification.htel_iff_dominates`, **no `Htel` certificate exists** for this
presentation: the `q = 1` numerator (`p = 1`, §1–§4) is exactly the boundary case
where the factorial presentation carries its own rate.  Rate is a property of the
pointing, not the real. -/

/-- General-`p` numerator: `a_{n+1} = (n+1)·q·a_n + p^{n+1}`
    (`a_n/dₙ = Σ_{k≤n}(p/q)ᵏ/k!`). -/
def expNum (p q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * q * expNum p q n + p ^ (n + 1)

/-- `p = 1` recovers the unit-fraction numerator. -/
theorem expNum_one (q : Nat) : ∀ n, expNum 1 q n = expUNum q n
  | 0 => rfl
  | n + 1 => by
    show (n + 1) * q * expNum 1 q n + 1 ^ (n + 1) = (n + 1) * q * expUNum q n + 1
    rw [expNum_one q n, Nat.one_pow]

/-- The general-`p` cross-determinant: `a_{i+1}·dᵢ = aᵢ·d_{i+1} + p^{i+1}·dᵢ`. -/
theorem exp_pq_cross_det (p q i : Nat) :
    expNum p q (i + 1) * expUDen q i
      = expNum p q i * expUDen q (i + 1) + p ^ (i + 1) * expUDen q i := by
  show ((i + 1) * q * expNum p q i + p ^ (i + 1)) * expUDen q i
      = expNum p q i * ((i + 1) * q * expUDen q i) + p ^ (i + 1) * expUDen q i
  ring_nat

/-- Cubic growth step: `(k+1)³ ≤ 2·k³` for `k ≥ 4`. -/
theorem cube_step (k : Nat) (hk : 4 ≤ k) :
    (k + 1) * (k + 1) * (k + 1) ≤ 2 * (k * k * k) := by
  obtain ⟨t, ht⟩ := Nat.le.dest hk
  rw [← ht]
  exact Nat.le.intro (show (4 + t + 1) * (4 + t + 1) * (4 + t + 1)
      + (t * t * t + 9 * (t * t) + 21 * t + 3)
      = 2 * ((4 + t) * (4 + t) * (4 + t)) from by ring_nat)

/-- `k³ < 2ᵏ` for `k ≥ 10` (stated at `k = 10 + s`). -/
theorem cube_lt_two_pow : ∀ s, (10 + s) * (10 + s) * (10 + s) < 2 ^ (10 + s)
  | 0 => by decide
  | s + 1 => by
    have hstep : (10 + s + 1) * (10 + s + 1) * (10 + s + 1)
        ≤ 2 * ((10 + s) * (10 + s) * (10 + s)) :=
      cube_step (10 + s) (Nat.le.intro (show 4 + (6 + s) = 10 + s from by ring_nat))
    have h2 : 2 * ((10 + s) * (10 + s) * (10 + s)) < 2 * 2 ^ (10 + s) :=
      E213.Meta.Nat.NatRing213.nat_mul_lt_mul_left (by decide) (cube_lt_two_pow s)
    show (10 + s + 1) * (10 + s + 1) * (10 + s + 1) < 2 ^ (10 + s + 1)
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ (10 + s)) 2]
    exact Nat.lt_of_le_of_lt hstep h2

/-- ★★★★ **The factorial presentation of `exp(p/q)` overtakes for `p ≥ 2`** (the ζ(3)
    mirror): at layer `i = q+9` the cross-determinant `p^{i+1}·dᵢ` exceeds the
    denominator quantum, so that layer is not dominated — the presentation is
    rate-free. -/
theorem exp_pq_presentation_overtakes (p q : Nat) (hp : 2 ≤ p) (hq : 1 ≤ q) :
    ∃ i, 1 ≤ i ∧
      ¬ E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification.Dominates
          (fun i => p ^ (i + 1) * expUDen q i) (expUDen q) i := by
  refine ⟨q + 9, Nat.le_add_left 1 (q + 8), ?_⟩
  apply E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification.overtake_breaks_layer
    _ (q + 9) (Nat.le_add_left 1 (q + 8))
  show (q + 10) * expUDen q (q + 10) < p ^ (q + 10) * expUDen q (q + 9)
  rw [show (q + 10) * expUDen q (q + 10)
        = ((q + 10) * (q + 10) * q) * expUDen q (q + 9) from by
        show (q + 10) * ((q + 10) * q * expUDen q (q + 9))
            = ((q + 10) * (q + 10) * q) * expUDen q (q + 9)
        ring_nat]
  apply E213.Meta.Nat.NatRing213.nat_mul_lt_mul_right (expUDen_pos q hq (q + 9))
  have h1 : (q + 10) * (q + 10) * q < (q + 10) * (q + 10) * (q + 10) :=
    E213.Meta.Nat.NatRing213.nat_mul_lt_mul_left
      (Nat.mul_pos (Nat.succ_pos (q + 9)) (Nat.succ_pos (q + 9)))
      (Nat.lt_add_of_pos_right (by decide))
  have h2 : (q + 10) * (q + 10) * (q + 10) < 2 ^ (q + 10) := by
    have h := cube_lt_two_pow q
    rw [Nat.add_comm 10 q] at h
    exact h
  have h3 : 2 ^ (q + 10) ≤ p ^ (q + 10) := Nat.pow_le_pow_left hp (q + 10)
  exact Nat.lt_of_lt_of_le (Nat.lt_trans h1 h2) h3

/-- ★★★★★ **No `Htel` certificate exists for the factorial presentation of
    `exp(p/q)`, `p ≥ 2`** — by the stratification biconditional
    (`htel_iff_dominates`), the overtaken layer kills every rate certificate.  The
    unit-fraction family (§4) is exactly the regime where this presentation carries
    its own rate; past it, completion must change the *pointing* (dyadic-bracket
    schedule à la `CubeRootTwoCut`) — rate is presentation-dependent, not a property
    of the real. -/
theorem exp_pq_no_htel (p q : Nat) (hp : 2 ≤ p) (hq : 1 ≤ q) :
    ¬ E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus.Htel (expNum p q) (expUDen q) := by
  intro h
  obtain ⟨i, hi, hnd⟩ := exp_pq_presentation_overtakes p q hp hq
  exact hnd
    ((E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification.htel_iff_dominates
        (fun i => p ^ (i + 1) * expUDen q i)
        (fun i => exp_pq_cross_det p q i)).mp h i hi)

end E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus
