import E213.Lib.Math.Logic.Omniscience
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.Logic.ChildSelection
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# vein-C CALIBRATION: the real equality-with-zero decision ⟺ WLPO

Companion to `RealDichotomyLLPO` (real *sign* decision = LLPO).  Here we pin the
real **equality-with-zero** decision = **WLPO**: deciding whether a corpus real
`x : Nat → Nat → Bool` *is* the canonical zero cut is exactly WLPO.

WLPO / the equality-decision are HYPOTHESES (`Prop` variables), never axioms.

## The encoding (all one sign — simpler than RD's alternating one)

Given an ARBITRARY `f : Nat → Bool` (no at-most-one restriction), encode the
non-negative real `xf f = Σ_n [f n] / 2^(n+1)`.  Layer-`L` numerator over `2^L`:

  `Q f 0 = 0`,  `Q f (L+1) = 2 * Q f L + (if f L then 1 else 0)`.

Key fact: `cutEq (xf f) zero ⟺ ∀ n, f n = false` (the sum is zero iff no bit
fires; any fire at `n` makes `Q f (n+1) ≥ 1`, monotone forward, so at probe
`(0, n+1)` the cut reads `false` while `zero` reads `true`).
-/

namespace E213.Lib.Math.Logic.RealEqualityWLPO

open E213.Lib.Math.Logic (WLPO)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — partial-sum numerator `Q f L` over denominator `2^L` -/

/-- Layer-`L` numerator of `xf f` over denominator `2^L`.  Doubling the
    denominator doubles the numerator; a fire at index `L` adds `+1` at the new
    denominator `2^{L+1}`. -/
def Q (f : Nat → Bool) : Nat → Nat
  | 0     => 0
  | L + 1 => 2 * Q f L + (if f L = true then 1 else 0)

/-- No fire anywhere keeps the numerator at `0` (value `0`). -/
theorem Q_zero_of_noFire (f : Nat → Bool) (h : ∀ n, f n = false) :
    ∀ L, Q f L = 0
  | 0     => rfl
  | L + 1 => by
    show 2 * Q f L + (if f L = true then 1 else 0) = 0
    rw [h L]
    show 2 * Q f L + 0 = 0
    rw [Nat.add_zero, Q_zero_of_noFire f h L, Nat.mul_zero]

/-- A fire at `L` makes the very next numerator at least `1`. -/
theorem one_le_Q_succ_of_fire (f : Nat → Bool) (L : Nat) (hfL : f L = true) :
    1 ≤ Q f (L + 1) := by
  show 1 ≤ 2 * Q f L + (if f L = true then 1 else 0)
  rw [hfL]
  show 1 ≤ 2 * Q f L + 1
  exact Nat.succ_le_succ (Nat.zero_le _)

/-- `Q` is monotone forward: `Q f L ≤ Q f (L + 1)` (a step only doubles + adds). -/
theorem Q_le_succ (f : Nat → Bool) (L : Nat) : Q f L ≤ Q f (L + 1) := by
  show Q f L ≤ 2 * Q f L + (if f L = true then 1 else 0)
  exact Nat.le_trans
    (Nat.le_trans (Nat.le_of_eq (Nat.one_mul (Q f L)).symm)
      (Nat.mul_le_mul_right (Q f L) (by decide : (1:Nat) ≤ 2)))
    (Nat.le_add_right _ _)

/-- `Q` is monotone: `a ≤ b → Q f a ≤ Q f b`. -/
theorem Q_mono (f : Nat → Bool) : ∀ a b, a ≤ b → Q f a ≤ Q f b := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Q_le_succ f _)

/-- A fire at `n` makes `Q f (k+1) ≥ 1` for every `k ≥ n` (the bit propagates
    forward). -/
theorem one_le_Q_of_fire (f : Nat → Bool) (n : Nat) (hfn : f n = true)
    (k : Nat) (hk : n ≤ k) : 1 ≤ Q f (k + 1) :=
  Nat.le_trans (one_le_Q_succ_of_fire f n hfn)
    (Q_mono f (n + 1) (k + 1) (Nat.succ_le_succ hk))

/-! ## §2 — the encoded cut and the canonical zero -/

/-- The encoded real `xf f` as a corpus cut: at resolution `k` it reads the
    layer-`(k+1)` approximant `Q f (k+1) / 2^(k+1)`. -/
def xf (f : Nat → Bool) : Nat → Nat → Bool :=
  fun m k => constCut (Q f (k + 1)) (2 ^ (k + 1)) m k

/-- The canonical zero cut: `constCut 0 1`, value `0`, `true` everywhere. -/
def zero : Nat → Nat → Bool := constCut 0 1

/-- `xf f m k = decide (Q f (k+1) * k ≤ 2^(k+1) * m)`. -/
theorem xf_eq (f : Nat → Bool) (m k : Nat) :
    xf f m k = decide (Q f (k + 1) * k ≤ 2 ^ (k + 1) * m) := rfl

/-- `zero m k = true` for every `m, k`. -/
theorem zero_true (m k : Nat) : zero m k = true := by
  show decide (0 * k ≤ 1 * m) = true
  apply decide_eq_true
  rw [Nat.zero_mul]
  exact Nat.zero_le _

/-! ## §3 — the two positivity lemmas -/

/-- **No fire ⟹ equals zero.**  If no bit fires, the numerator is `0` at every
    layer, so `Q f (k+1) * k = 0 ≤ 2^(k+1) * m`; the cut reads `true` = `zero`. -/
theorem cutEq_zero_of_noFire (f : Nat → Bool) (h : ∀ n, f n = false) :
    cutEq (xf f) zero := by
  intro m k
  rw [zero_true, xf_eq]
  apply decide_eq_true
  rw [Q_zero_of_noFire f h (k + 1), Nat.zero_mul]
  exact Nat.zero_le _

/-- **A fire ⟹ NOT equal to zero** (the technical heart).  A fire at `n` gives
    `Q f (n+2) ≥ 1`, so at probe `(0, n+1)` the cut reads `false`
    (`Q f (n+2) * (n+1) ≥ 1 > 0 = 2^(n+2) * 0`) while `zero` reads `true`. -/
theorem not_cutEq_zero_of_fire (f : Nat → Bool) (n : Nat) (hfn : f n = true) :
    ¬ cutEq (xf f) zero := by
  intro heq
  -- probe at m = 0, k = n+1.  Q f (k+1) = Q f (n+2) ≥ 1, k = n+1 ≥ 1.
  have hQ : 1 ≤ Q f (n + 1 + 1) :=
    one_le_Q_of_fire f n hfn (n + 1) (Nat.le_succ n)
  have hk : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  -- Q f (n+2) * (n+1) ≥ 1*1 = 1 > 0
  have hgt : 2 ^ (n + 1 + 1) * 0 < Q f (n + 1 + 1) * (n + 1) := by
    rw [Nat.mul_zero]
    exact Nat.lt_of_lt_of_le (by decide : (0:Nat) < 1)
      (Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
        (Nat.mul_le_mul hQ hk))
  -- so xf reads false at (0, n+1)
  have hfalse : xf f 0 (n + 1) = false := by
    rw [xf_eq]
    exact decide_eq_false (Nat.not_le.mpr hgt)
  -- but heq forces xf = zero = true
  have := heq 0 (n + 1)
  rw [zero_true, hfalse] at this
  exact Bool.noConfusion this

/-! ## §4 — the equality-with-zero characterization -/

/-- ★ **The heart**: `cutEq (xf f) zero ↔ ∀ n, f n = false`.  The encoded sum is
    the zero cut iff no bit fires. -/
theorem xf_eq_zero_iff (f : Nat → Bool) :
    cutEq (xf f) zero ↔ ∀ n, f n = false := by
  apply Iff.intro
  · intro heq n
    exact E213.Lib.Math.Logic.ne_true_imp_false (f n)
      (fun hfn => not_cutEq_zero_of_fire f n hfn heq)
  · intro h
    exact cutEq_zero_of_noFire f h

/-! ## §5 — the calibration: real equality-with-zero decision ⟺ WLPO -/

/-- **Real equality-with-zero decision**: for the canonical zero cut, decide for
    every corpus real whether it equals zero. -/
def RealEqDecision : Prop :=
  ∀ x : Nat → Nat → Bool, cutEq x zero ∨ ¬ cutEq x zero

/-- ★★★ **Deciding real-equality-with-zero implies WLPO** — the forward
    calibration (the second leg of the sign/equality/apartness ↔ LLPO/WLPO/MP
    triad).  Feed the decision hypothesis the encoded real `xf f`:
      `cutEq (xf f) zero` ⟹ `∀ n, f n = false`   (left WLPO disjunct);
      `¬ cutEq (xf f) zero` ⟹ `¬ ∀ n, f n = false` (right WLPO disjunct).
    ∅-axiom: `RealEqDecision` is a `Prop` hypothesis, never an axiom. -/
theorem wlpo_of_realEqDecision (hdec : RealEqDecision) : WLPO :=
  fun f =>
    (hdec (xf f)).elim
      (fun heq => Or.inl ((xf_eq_zero_iff f).mp heq))
      (fun hne => Or.inr (fun hall => hne ((xf_eq_zero_iff f).mpr hall)))

/-- ★★ **Converse (on the encoded reals): WLPO ⟹ the encoded equality-decision.**
    WLPO on `f` decides `∀ n, f n = false`; map through `xf_eq_zero_iff` to the
    cut-equality decision.  Together with `wlpo_of_realEqDecision` this is the
    two-sided calibration: *the encoded equality-with-zero decision is exactly
    WLPO*. -/
theorem encodedEqDecision_of_wlpo (hwlpo : WLPO) (f : Nat → Bool) :
    cutEq (xf f) zero ∨ ¬ cutEq (xf f) zero :=
  (hwlpo f).elim
    (fun hall => Or.inl ((xf_eq_zero_iff f).mpr hall))
    (fun hnot => Or.inr (fun heq => hnot ((xf_eq_zero_iff f).mp heq)))

end E213.Lib.Math.Logic.RealEqualityWLPO
