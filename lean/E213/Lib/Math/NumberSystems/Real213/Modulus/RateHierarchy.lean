import E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
import E213.Meta.Nat.PowBernoulli

/-!
# RateHierarchy — the modulus-degree ladder is infinite and strict

`RateStratification` exhibited the degree axis with a single witness: `sepDen`
(degree 2) is `rootFloor 2`-dominated everywhere yet breaks the identity
(degree-1) schedule at layer 4.  This file promotes that lone witness to a
**uniform parametric family**, closing the gap that "degree ≥ 3 is only named,
not built": for *every* `t`, the degree axis genuinely outruns degree `t`.

## The family

`sepDenS s` is the presentation with denominator step
`d_{i+1} = (⌊i^{1/s}⌋ + 2)·d_i` and cross-determinant `W = d` (the numerators
`sepNumS s`, `a_{i+1} = (⌊i^{1/s}⌋+2)·a_i + 1`, realize it exactly over ℕ).
`sepDenS 2` is the `RateStratification.sepDen` witness; this is its generalization
to all degrees.

  * ★★★ `sepDenS_dominatesS_all` — for every `s`, `sepDenS s` is
    `rootFloor s`-dominated at *every* layer (the degree-`s` rescue): the same
    `⌊·^{1/s}⌋ ≤ 2·⌊·^{1/s}⌋` monotonicity that rescued the degree-2 witness.
  * ★★★ `sepDenS_breaks` — for every `t ≥ 2`, the degree-`(t+1)` presentation
    `sepDenS (t+1)` is **not** `rootFloor t`-dominated at layer `(t+3)^t`.  The
    proof reads the layer as a perfect `t`-th power: both schedule probes there
    equal `t+3`, while the denominator's growth coefficient `⌊((t+3)^t)^{1/(t+1)}⌋`
    is forced below `t+1` by the cross-degree power gap
    `PowBernoulli.pow_pred_lt : (t+3)^t < (t+2)^(t+1)`.
  * ★★★ `strict_modulus_hierarchy` — the two together: every consecutive pair of
    integer rungs `(t, t+1)` is separated by an explicit presentation, so the
    modulus-degree ladder is infinite and each rung strictly larger than the last.
  * ★★ `sepS_graded_modulus` — the actual real `sepNumS s / sepDenS s` completes
    with the constructed total ∅-axiom modulus `N(m,k) = k^s + 1`
    (`graded_total_modulus`).  Combined with `sepDenS_breaks`, the real
    `sepNumS (t+1) / sepDenS (t+1)` is an honest inhabitant of modulus degree
    exactly `t+1` for every `t` — the ladder's rungs are all occupied.

Narrative: `theory/math/analysis/holonomic_modulus.md` §4; the cross-degree gap
is `theory/math/analysis` infra (`Meta/Nat/PowBernoulli`).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.RateHierarchy

open E213.Lib.Math.NumberSystems.Real213.Modulus.RateStratification
  (DominatesS Dominates dominatedS_graded_modulus htel_of_dominates_all)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (Htel rcut hmono_of_hmonoS)
open E213.Meta.Nat.RootFloor
  (rootFloor rootFloor_mono rootFloor_pow rootFloor_pos rootFloor_pow_le)
open E213.Meta.Nat.PowBasic (powBase_le one_le_pow)
open E213.Meta.Nat.PowBernoulli (pow_pred_lt succ_pow_lt_succ_pow)
open E213.Tactic.NatHelper (add_mul mul_assoc le_of_add_le_add_left)

/-! ## §1 — the parametric denominator family -/

/-- The degree-`s` separation denominator: `d_{i+1} = (⌊i^{1/s}⌋ + 2)·d_i`,
    paired with cross-determinant `W = d`.  `sepDenS 2 = RateStratification.sepDen`. -/
def sepDenS (s : Nat) : Nat → Nat
  | 0 => 1
  | i+1 => (rootFloor s i + 2) * sepDenS s i

theorem sepDenS_pos (s i : Nat) : 1 ≤ sepDenS s i := by
  induction i with
  | zero => exact Nat.le_refl 1
  | succ i ih => exact Nat.mul_pos (Nat.succ_le_succ (Nat.zero_le _)) ih

/-! ## §2 — the degree-`s` rescue (dominated at every layer) -/

/-- ★★★ **The degree-`s` schedule rescues `sepDenS s`.**  With `W = d = sepDenS s`,
    every layer is dominated under `ρ = rootFloor s`: the comparison reduces to
    `⌊i^{1/s}⌋ ≤ 2·⌊(i+1)^{1/s}⌋`, which monotonicity of the root supplies.  The
    uniform-in-`s` generalization of `RateStratification.sep_dominatesS_all`. -/
theorem sepDenS_dominatesS_all (s i : Nat) :
    DominatesS (sepDenS s) (sepDenS s) (rootFloor s) i := by
  show rootFloor s i * rootFloor s (i+1) * sepDenS s i + rootFloor s i * sepDenS s i
      ≤ rootFloor s (i+1) * sepDenS s (i+1)
  have hmono : rootFloor s i ≤ rootFloor s (i+1) := rootFloor_mono s (Nat.le_succ i)
  have hcoef : rootFloor s i * rootFloor s (i+1) + rootFloor s i
      ≤ rootFloor s (i+1) * (rootFloor s i + 2) := by
    rw [Nat.mul_add, Nat.mul_comm (rootFloor s (i+1)) (rootFloor s i)]
    exact Nat.add_le_add_left
      (Nat.le_trans hmono (by rw [Nat.mul_two]; exact Nat.le_add_right _ _)) _
  calc rootFloor s i * rootFloor s (i+1) * sepDenS s i + rootFloor s i * sepDenS s i
      = (rootFloor s i * rootFloor s (i+1) + rootFloor s i) * sepDenS s i :=
        (add_mul _ _ _).symm
    _ ≤ (rootFloor s (i+1) * (rootFloor s i + 2)) * sepDenS s i :=
        Nat.mul_le_mul_right _ hcoef
    _ = rootFloor s (i+1) * ((rootFloor s i + 2) * sepDenS s i) := mul_assoc _ _ _
    _ = rootFloor s (i+1) * sepDenS s (i+1) := rfl

/-! ## §3 — the cross-degree break (not dominated one rung down) -/

/-- Read-back calibration: for `t ≥ 2`, the `t`-th root floor of `K^t + 1` is
    exactly `K` (it cannot reach `K+1` because `K^t + 1 < (K+1)^t`). -/
theorem rootFloor_succ_eq (t K : Nat) (ht : 2 ≤ t) (hK : 1 ≤ K) :
    rootFloor t (K^t + 1) = K := by
  have ht1 : 1 ≤ t := Nat.le_of_succ_le ht
  have hlow : K ≤ rootFloor t (K^t + 1) := by
    have h1 : rootFloor t (K^t) ≤ rootFloor t (K^t + 1) :=
      rootFloor_mono t (Nat.le_succ (K^t))
    rwa [rootFloor_pow t ht1 K] at h1
  have hup : rootFloor t (K^t + 1) ≤ K := by
    rcases Nat.lt_or_ge (rootFloor t (K^t + 1)) (K+1) with h | h
    · exact Nat.le_of_lt_succ h
    · exfalso
      have hR'pos : 1 ≤ rootFloor t (K^t + 1) :=
        rootFloor_pos t _ (Nat.succ_le_succ (Nat.zero_le _))
      have h1 : (K+1)^t ≤ (rootFloor t (K^t + 1))^t := powBase_le h t
      have h2 : (rootFloor t (K^t + 1))^t ≤ K^t + 1 := rootFloor_pow_le t (K^t + 1) hR'pos
      have h3 : K^t + 1 < (K+1)^t := succ_pow_lt_succ_pow t K ht hK
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 (Nat.le_trans h1 h2))
  exact Nat.le_antisymm hup hlow

/-- ★★★ **The degree-`t` schedule breaks `sepDenS (t+1)`.**  At the perfect
    `t`-th power layer `i = (t+3)^t`, both `rootFloor t` probes read `t+3`, while
    the denominator's growth coefficient `rootFloor (t+1) i + 2` is forced below
    `t+3` by `pow_pred_lt` — so the per-layer budget is overrun and the layer is
    not dominated.  For every `t ≥ 2` this places `sepDenS (t+1)` strictly above
    rung `t`. -/
theorem sepDenS_breaks (t : Nat) (ht : 2 ≤ t) :
    ¬ DominatesS (sepDenS (t+1)) (sepDenS (t+1)) (rootFloor t) ((t+2+1)^t) := by
  have ht1 : 1 ≤ t := Nat.le_of_succ_le ht
  intro hdom
  -- abbreviate the perfect `t`-th power layer as `i` (core `generalize`, goal-only)
  revert hdom
  generalize hi : (t+2+1)^t = i
  intro hdom
  have hdpos : 1 ≤ sepDenS (t+1) i := sepDenS_pos (t+1) i
  -- the two `rootFloor t` probes at the perfect `t`-th power layer both read `t+3`
  have ha : rootFloor t i = t+2+1 := by rw [← hi]; exact rootFloor_pow t ht1 (t+2+1)
  have hb : rootFloor t (i+1) = t+2+1 := by
    rw [← hi]; exact rootFloor_succ_eq t (t+2+1) ht (Nat.succ_le_succ (Nat.zero_le _))
  -- the growth coefficient is forced below `t+1`
  have hR : rootFloor (t+1) i ≤ t+1 := by
    rw [← hi]
    rcases Nat.lt_or_ge (rootFloor (t+1) ((t+2+1)^t)) (t+2) with h | h
    · exact Nat.le_of_lt_succ h
    · exfalso
      have hRpos : 1 ≤ rootFloor (t+1) ((t+2+1)^t) :=
        rootFloor_pos (t+1) _ (one_le_pow (Nat.succ_le_succ (Nat.zero_le _)) t)
      have h1 : (t+2)^(t+1) ≤ (rootFloor (t+1) ((t+2+1)^t))^(t+1) := powBase_le h (t+1)
      have h2 : (rootFloor (t+1) ((t+2+1)^t))^(t+1) ≤ (t+2+1)^t :=
        rootFloor_pow_le (t+1) ((t+2+1)^t) hRpos
      have h3 : (t+2+1)^t < (t+2)^(t+1) := pow_pred_lt t (t+2) (Nat.le_refl _)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 (Nat.le_trans h1 h2))
  -- assemble the contradiction: the per-layer inequality forces `(t+3)·d ≤ 0`
  have hdom0 : rootFloor t i * rootFloor t (i+1) * sepDenS (t+1) i
        + rootFloor t i * sepDenS (t+1) i
      ≤ rootFloor t (i+1) * sepDenS (t+1) (i+1) := hdom
  have hsucc : sepDenS (t+1) (i+1) = (rootFloor (t+1) i + 2) * sepDenS (t+1) i := rfl
  rw [ha, hb, hsucc] at hdom0
  have hRB : rootFloor (t+1) i + 2 ≤ t+2+1 := Nat.add_le_add_right hR 2
  have hstep1 : (rootFloor (t+1) i + 2) * sepDenS (t+1) i
      ≤ (t+2+1) * sepDenS (t+1) i := Nat.mul_le_mul_right _ hRB
  have hchain : (t+2+1) * (t+2+1) * sepDenS (t+1) i + (t+2+1) * sepDenS (t+1) i
      ≤ (t+2+1) * (t+2+1) * sepDenS (t+1) i := by
    calc (t+2+1) * (t+2+1) * sepDenS (t+1) i + (t+2+1) * sepDenS (t+1) i
        ≤ (t+2+1) * ((rootFloor (t+1) i + 2) * sepDenS (t+1) i) := hdom0
      _ ≤ (t+2+1) * ((t+2+1) * sepDenS (t+1) i) := Nat.mul_le_mul_left _ hstep1
      _ = (t+2+1) * (t+2+1) * sepDenS (t+1) i := (mul_assoc _ _ _).symm
  have hle0 : (t+2+1) * sepDenS (t+1) i ≤ 0 := by
    have h : (t+2+1) * (t+2+1) * sepDenS (t+1) i + (t+2+1) * sepDenS (t+1) i
        ≤ (t+2+1) * (t+2+1) * sepDenS (t+1) i + 0 :=
      Nat.le_trans hchain (Nat.le_of_eq (Nat.add_zero _).symm)
    exact le_of_add_le_add_left h
  exact absurd
    (Nat.le_trans (Nat.mul_pos (Nat.succ_le_succ (Nat.zero_le _)) hdpos) hle0)
    (by decide)

/-! ## §4 — the strict infinite ladder + the occupied rungs -/

/-- ★★★ **The modulus-degree ladder is infinite and strict.**  For every
    `t ≥ 2`, the presentation `sepDenS (t+1)` is dominated at every layer under
    the degree-`(t+1)` schedule yet fails the degree-`t` schedule at layer
    `(t+3)^t` — separating consecutive integer rungs `(t, t+1)`.  Together with
    `RateStratification.sep_*` (the `(1,2)` rung) every rung step is witnessed. -/
theorem strict_modulus_hierarchy (t : Nat) (ht : 2 ≤ t) :
    (∀ i, DominatesS (sepDenS (t+1)) (sepDenS (t+1)) (rootFloor (t+1)) i)
    ∧ ¬ DominatesS (sepDenS (t+1)) (sepDenS (t+1)) (rootFloor t) ((t+2+1)^t) :=
  ⟨sepDenS_dominatesS_all (t+1), sepDenS_breaks t ht⟩

/-! ## §5 — the rungs are occupied by actual reals -/

/-- The convergent numerators realizing `sepDenS s` as an actual presentation:
    `a_{i+1} = (⌊i^{1/s}⌋+2)·a_i + 1` makes the cross-determinant exactly
    `sepDenS s` (no division — the recurrence solves the cross-det over ℕ). -/
def sepNumS (s : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => (rootFloor s i + 2) * sepNumS s i + 1

/-- The presentation's cross-determinant is `sepDenS s` itself (`W = d`). -/
theorem sep_cross_detS (s i : Nat) :
    sepNumS s (i+1) * sepDenS s i = sepNumS s i * sepDenS s (i+1) + sepDenS s i := by
  show ((rootFloor s i + 2) * sepNumS s i + 1) * sepDenS s i
      = sepNumS s i * ((rootFloor s i + 2) * sepDenS s i) + sepDenS s i
  rw [add_mul, Nat.one_mul, ← mul_assoc, Nat.mul_comm (sepNumS s i) (rootFloor s i + 2)]

/-- The convergents are strictly increasing (the cross-det is positive). -/
theorem sep_hmonoS_S (s i : Nat) :
    sepNumS s i * sepDenS s (i+1) < sepNumS s (i+1) * sepDenS s i := by
  rw [sep_cross_detS s i]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.add_le_add_left (sepDenS_pos s i) _)

/-- ★★ **Each rung is occupied by an actual real.**  The presentation
    `sepNumS s / sepDenS s` completes through the degree-`s` root schedule with
    the constructed total ∅-axiom modulus `N(m,k) = k^s + 1`.  At `s = t+1`,
    `sepDenS_breaks` shows this real is *not* completable one rung down — so its
    modulus degree is exactly `t+1`, for every `t`. -/
theorem sepS_graded_modulus (s : Nat) (hs : 1 ≤ s) (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (sepNumS s) (sepDenS s) i m k = rcut (sepNumS s) (sepDenS s) j m k :=
  dominatedS_graded_modulus s hs (sepDenS s) (sepDenS_pos s) (sep_cross_detS s)
    (fun i _ => sepDenS_dominatesS_all s i)
    (hmono_of_hmonoS (sepDenS_pos s) (sep_hmonoS_S s)) (sep_hmonoS_S s) m k hk

/-! ## §6 — the dual: degree 1 is generously inhabited (any cross-determinant) -/

/-- The fast denominator taming an arbitrary cross-determinant `W`:
    `d_{i+1} = i·W_i + d_i` (`d_0 = 1`).  Built so the identity schedule's
    per-layer budget always clears `W`, no matter how large. -/
def fastDen (W : Nat → Nat) : Nat → Nat
  | 0 => 1
  | i+1 => i * W i + fastDen W i

/-- ★★★ **Any cross-determinant is degree-1 with a fast-enough denominator.**
    For *every* `W` — however large, even unbounded — `fastDen W` is dominated by
    the identity (degree-1) schedule at every layer.  So the free, linear-modulus
    class is *not* the unimodular `W ≡ 1` floor alone: a presentation with a huge
    cross-determinant is still degree 1 once its denominators outpace `W` per
    layer.  The race is `W`-growth vs `d`-growth, not the size of `W` itself.

    The actual-real witness with **unbounded** `W` is already in the repo: e's
    factorial presentation (`d_i = i!`) has `W_i = i!` yet completes at `N = k+2`
    (`HolonomicReal.euler_total_modulus`).  The "good news": a cheap (term-count)
    modulus needs only fast denominators, not the optimal continued fraction —
    though the cost relocates into the *size* of each term, not vanishing. -/
theorem fastDen_dominates (W : Nat → Nat) (i : Nat) : Dominates W (fastDen W) i := by
  show i*(i+1)*W i + i*(fastDen W i) ≤ (i+1)*(fastDen W (i+1))
  have hd : fastDen W (i+1) = i * W i + fastDen W i := rfl
  rw [hd]
  calc i*(i+1)*W i + i*(fastDen W i)
      ≤ i*(i+1)*W i + (i+1)*(fastDen W i) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
    _ = (i+1)*(i * W i + fastDen W i) := by ring_nat

/-- Any presentation realizing `(W, fastDen W)` carries the rate certificate, so
    it completes freely (`N(m,k) = k+2`) — regardless of how large `W` grows. -/
theorem fastDen_carries_Htel (W a : Nat → Nat)
    (hW : ∀ i, a (i+1) * fastDen W i = a i * fastDen W (i+1) + W i) :
    Htel a (fastDen W) :=
  htel_of_dominates_all W hW (fun i _ => fastDen_dominates W i)

end E213.Lib.Math.NumberSystems.Real213.Modulus.RateHierarchy
