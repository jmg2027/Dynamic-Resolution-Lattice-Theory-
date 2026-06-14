import E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
import E213.Meta.Nat.RootFloor

/-!
# DegreeCriterion — the precise relationship between the cross-determinant and degree

`RateStratification` reduced completability to scheduled domination `DominatesS`;
`RateHierarchy` showed the schedule degree is a strict infinite ladder.  This file
pins **what fixes the degree**: the race between the cross-determinant `W` and the
denominator's *increment*, probed by the schedule.

Dividing the degree-`s` domination `ρ_i·ρ_{i+1}·W_i + ρ_i·d_i ≤ ρ_{i+1}·d_{i+1}`
(with `ρ = rootFloor s`, monotone) by `ρ_{i+1}` brackets the condition between two
clean inequalities, differing only by the single term `d_i`:

  * ★★★ `dominatesS_of_scheduled_increment` — **sufficient**: if the probed
    cross-determinant fits under the denominator *increment*,
    `ρ_i·W_i + d_i ≤ d_{i+1}`, then layer `i` is dominated.  (`degree_le_of_increment`
    is the `rootFloor s` form: the whole presentation is degree ≤ s.)
  * ★★★ `scheduled_le_of_dominatesS` — **necessary**: domination forces the probed
    cross-determinant under the *next denominator*, `ρ_i·W_i ≤ d_{i+1}`.
    (`not_dominatesS_of_overtake`: `d_{i+1} < ⌊i^{1/s}⌋·W_i` at any layer breaks it.)
  * `degree_criterion_bracket` — the two-sided statement at one layer; the gap is
    exactly `d_i`.

The threshold is monotone in the degree (`increment_criterion_mono`, via
`rootFloor_antitone_degree`: a bigger `s` shrinks the probe), so "meets the
degree-`s` increment criterion" is upward-closed — a well-defined degree ceiling.

Two readings of the boundary:
  * the degree-1 saturation `i·W_i + d_i = d_{i+1}` is exactly `RateHierarchy.fastDen`
    and e's factorial presentation (`W = i!`, `d_{i+1} = (i+1)·d_i`) — the free
    bottom rung sits right on the increment criterion;
  * the strict hierarchy `RateHierarchy.sepDenS_breaks` is the necessary side
    failing: `d_{i+1} < ⌊i^{1/(t)}⌋·W_i` at the perfect-power layer.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.DegreeCriterion

open E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification (DominatesS)
open E213.Meta.Nat.RootFloor
  (rootFloor rootFloor_mono rootFloor_pos rootFloor_pow_le rootFloor_le le_rootFloorGo)
open E213.Meta.Nat.PowBasic (one_le_pow)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Tactic.NatHelper (mul_assoc le_of_mul_le_mul_right)

/-! ## §1 — the two-sided criterion (any monotone schedule) -/

/-- ★★★ **Sufficient.**  If the schedule is monotone (`ρ_i ≤ ρ_{i+1}`) and the
    probed cross-determinant fits under the denominator increment
    (`ρ_i·W_i + d_i ≤ d_{i+1}`), layer `i` is `ρ`-dominated. -/
theorem dominatesS_of_scheduled_increment (W d ρ : Nat → Nat) (i : Nat)
    (hρ : ρ i ≤ ρ (i+1)) (h : ρ i * W i + d i ≤ d (i+1)) :
    DominatesS W d ρ i := by
  show ρ i * ρ (i+1) * W i + ρ i * d i ≤ ρ (i+1) * d (i+1)
  have hm : ρ (i+1) * (ρ i * W i + d i) ≤ ρ (i+1) * d (i+1) := Nat.mul_le_mul_left _ h
  have hstep : ρ i * ρ (i+1) * W i + ρ i * d i ≤ ρ (i+1) * (ρ i * W i + d i) := by
    rw [Nat.mul_add]
    have e1 : ρ i * ρ (i+1) * W i = ρ (i+1) * (ρ i * W i) := by
      rw [Nat.mul_comm (ρ i) (ρ (i+1)), mul_assoc]
    rw [e1]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hρ) _
  exact Nat.le_trans hstep hm

/-- ★★★ **Necessary.**  `ρ`-domination at layer `i` forces the probed
    cross-determinant under the next denominator: `ρ_i·W_i ≤ d_{i+1}`. -/
theorem scheduled_le_of_dominatesS (W d ρ : Nat → Nat) (i : Nat)
    (hρ1 : 1 ≤ ρ (i+1)) (hdom : DominatesS W d ρ i) :
    ρ i * W i ≤ d (i+1) := by
  have h : ρ i * ρ (i+1) * W i + ρ i * d i ≤ ρ (i+1) * d (i+1) := hdom
  have h2 : ρ i * ρ (i+1) * W i ≤ ρ (i+1) * d (i+1) :=
    Nat.le_trans (Nat.le_add_right _ _) h
  have e1 : ρ i * ρ (i+1) * W i = (ρ i * W i) * ρ (i+1) := by
    rw [mul_assoc, Nat.mul_comm (ρ (i+1)) (W i), ← mul_assoc]
  have e2 : ρ (i+1) * d (i+1) = d (i+1) * ρ (i+1) := Nat.mul_comm _ _
  rw [e1, e2] at h2
  exact le_of_mul_le_mul_right hρ1 h2

/-! ## §2 — the `rootFloor s` degree readings -/

/-- ★★★ **Degree ≤ s, from the increment criterion.**  If the degree-`s` probe of
    the cross-determinant fits under the denominator increment at every layer, the
    presentation is dominated at every layer (degree ≤ s). -/
theorem degree_le_of_increment (s : Nat) (W d : Nat → Nat)
    (h : ∀ i, rootFloor s i * W i + d i ≤ d (i+1)) (i : Nat) :
    DominatesS W d (rootFloor s) i :=
  dominatesS_of_scheduled_increment W d (rootFloor s) i
    (rootFloor_mono s (Nat.le_succ i)) (h i)

/-- ★★★ **Overtake breaks the layer.**  If the next denominator falls below the
    degree-`s` probe of the cross-determinant (`d_{i+1} < ⌊i^{1/s}⌋·W_i`), layer `i`
    is not dominated — the necessary side, contrapositive. -/
theorem not_dominatesS_of_overtake (s : Nat) (W d : Nat → Nat) (i : Nat)
    (hover : d (i+1) < rootFloor s i * W i) :
    ¬ DominatesS W d (rootFloor s) i := by
  intro hdom
  have hρ1 : 1 ≤ rootFloor s (i+1) :=
    rootFloor_pos s (i+1) (Nat.succ_le_succ (Nat.zero_le i))
  exact absurd (scheduled_le_of_dominatesS W d (rootFloor s) i hρ1 hdom)
    (Nat.not_le.mpr hover)

/-- The two-sided criterion at one layer: domination is bracketed between
    `⌊i^{1/s}⌋·W_i + d_i ≤ d_{i+1}` (sufficient) and `⌊i^{1/s}⌋·W_i ≤ d_{i+1}`
    (necessary) — the gap is exactly the single term `d_i`. -/
theorem degree_criterion_bracket (s : Nat) (W d : Nat → Nat) (i : Nat) :
    (rootFloor s i * W i + d i ≤ d (i+1) → DominatesS W d (rootFloor s) i)
    ∧ (DominatesS W d (rootFloor s) i → rootFloor s i * W i ≤ d (i+1)) :=
  ⟨fun h => dominatesS_of_scheduled_increment W d (rootFloor s) i
      (rootFloor_mono s (Nat.le_succ i)) h,
   fun hdom => scheduled_le_of_dominatesS W d (rootFloor s) i
      (rootFloor_pos s (i+1) (Nat.succ_le_succ (Nat.zero_le i))) hdom⟩

/-! ## §3 — the criterion is monotone in the degree -/

/-- Exponent monotonicity for a base `≥ 1`: `a^s ≤ a^{s'}` when `s ≤ s'`. -/
theorem pow_le_pow_exp {a s s' : Nat} (ha : 1 ≤ a) (hss : s ≤ s') : a^s ≤ a^s' := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hss
  rw [pow_add]
  calc a^s = a^s * 1 := (Nat.mul_one _).symm
    _ ≤ a^s * a^t := Nat.mul_le_mul_left _ (one_le_pow ha t)

/-- The integer root floor is **antitone in the degree**: a larger root index
    gives a smaller floor (`s ≤ s' ⟹ rootFloor s' x ≤ rootFloor s x`).  A bigger
    `s` is a slower probe. -/
theorem rootFloor_antitone_degree {s s' : Nat} (hss : s ≤ s') (x : Nat) :
    rootFloor s' x ≤ rootFloor s x := by
  rcases Nat.eq_zero_or_pos (rootFloor s' x) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hle : (rootFloor s' x)^s' ≤ x := rootFloor_pow_le s' x hpos
    have hpow : (rootFloor s' x)^s ≤ (rootFloor s' x)^s' := pow_le_pow_exp hpos hss
    exact le_rootFloorGo s x (rootFloor s' x) (Nat.le_trans hpow hle) x (rootFloor_le s' x)

/-- ★★ **The increment criterion is upward-closed in the degree.**  If a
    presentation meets the degree-`s` increment criterion at layer `i`, it meets
    every higher degree `s' ≥ s` there — so "degree ≤ s" is a genuine ceiling, and
    by `degree_le_of_increment` the presentation is dominated at all `s' ≥ s`. -/
theorem increment_criterion_mono {s s' : Nat} (hss : s ≤ s')
    (W d : Nat → Nat) (i : Nat)
    (h : rootFloor s i * W i + d i ≤ d (i+1)) :
    rootFloor s' i * W i + d i ≤ d (i+1) :=
  Nat.le_trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (W i) (rootFloor_antitone_degree hss i)) (d i))
    h

end E213.Lib.Math.NumberSystems.Real213.Modulus.DegreeCriterion
