import E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus
import E213.Meta.Nat.PowBasic

/-!
# ModulusComposition — schedules with irrational degree: receipts taking receipts

The modulus-degree ladder's rungs so far are integer-indexed (`N = k+2`,
`N = 3k+5`, the open `N = k^s`).  This file makes the **degree slot itself a
cut**: from an exponent real τ — given as a decidable cut `c` with an integer
upper witness — build the schedule

    `powSched c B k = ⌈ k ^ (p_k / 2^k) ⌉`,   `p_k` = dyadic upper reading of τ,

entirely in `ℕ` (`dyUp` reads the numerator off the cut level by level;
`rootCeil` takes the `2^k`-th root ceiling).  Evaluating the schedule *queries
the exponent's cut*, and when that cut is a `CauchyCutSeq` limit the query
evaluates its modulus field — **a modulus calling another real's modulus as a
subroutine**.  That is the operational content of "irrational degree": the
receipt ladder becomes a call tree of folds.

  * **Spec** (`powSched_sound` / `powSched_least`): the value is the exact
    integer ceiling of `k^(p/2^k)` — sandwiched by `2^k`-th powers.
  * **Calibration** (`powSched_rat`): an integer exponent `s` (as the rational
    cut `decide (s·k ≤ m)`) gives back exactly `k^s` — the functional extends
    the polynomial ladder.
  * **Degree ∛2** (`cbrtPow_at_two`): the ladder eats its own degree-3 brick
    as an exponent — `powSched cbrt2Cut 2 2 = 3` (`= ⌈2^{6/4}⌉ = ⌈2^{3/2}⌉`),
    with the generic upper-soundness discharged by `cbrt2Cut_double`.
  * **Degree e** (`ePow_at_two`): `powSched eulerModCut 3 2 = 7`
    (`= ⌈2^{11/4}⌉`, `e ≤ 11/4 = 2.75`), where `eulerModCut` reads e through
    `eulerCauchySeq.N` — the kernel evaluates e's constructed modulus inside
    the schedule, by `decide`.
  * **The cascade's first rung** (`eSelfScheduled`): rescheduling
    (`reschedule`, limit-preserving) e's own `CauchyCutSeq` by a schedule that
    queries e — e presented with its modulus computed *through* its modulus.
    Honest scope: this is the operational (call-tree) cascade, not the
    `μ(τ) = τ` fixed point of the degree dynamics, which stays a frontier.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.ModulusComposition

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut (cube cbrt2Cut cube_double)
open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus (eulerCauchySeq)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.PowBasic
  (powBase_le one_pow_pure one_le_pow powBase_lt self_le_pow pow_mul_pure)
open E213.Tactic.NatHelper (mul_assoc mul_left_comm lt_of_le_lt)

/-! ## §1 — `rootCeil`: the exact integer `q`-th root ceiling -/

/-- Bounded descent: least `M ≤ F` with `x ≤ M^q` (when the bound works). -/
def rootCeilGo (q x : Nat) : Nat → Nat
  | 0 => 0
  | M+1 => cond (decide (x ≤ M^q)) (rootCeilGo q x M) (M+1)

/-- `⌈x^{1/q}⌉`: least `M` with `x ≤ M^q` (searching below `x` itself). -/
def rootCeil (q x : Nat) : Nat := rootCeilGo q x x

theorem rootCeilGo_sound (q x : Nat) : ∀ F, x ≤ F^q → x ≤ (rootCeilGo q x F)^q
  | 0, h => h
  | F+1, h => by
      show x ≤ (cond (decide (x ≤ F^q)) (rootCeilGo q x F) (F+1))^q
      by_cases hF : x ≤ F^q
      · rw [decide_eq_true hF]; exact rootCeilGo_sound q x F hF
      · rw [decide_eq_false hF]; exact h

theorem rootCeilGo_least (q x : Nat) : ∀ F m, m < rootCeilGo q x F → ¬ (x ≤ m^q)
  | 0, m, hm => absurd hm (Nat.not_lt_zero m)
  | F+1, m, hm => by
      by_cases hF : x ≤ F^q
      · rw [show rootCeilGo q x (F+1) = rootCeilGo q x F from by
              show cond (decide (x ≤ F^q)) _ _ = _
              rw [decide_eq_true hF]; rfl] at hm
        exact rootCeilGo_least q x F m hm
      · rw [show rootCeilGo q x (F+1) = F+1 from by
              show cond (decide (x ≤ F^q)) _ _ = _
              rw [decide_eq_false hF]; rfl] at hm
        intro hxm
        exact hF (Nat.le_trans hxm (powBase_le (Nat.le_of_lt_succ hm) q))

/-- `rootCeil` is sound as soon as `1 ≤ q`: `x` itself bounds its `q`-th root. -/
theorem rootCeil_sound (q x : Nat) (hq : 1 ≤ q) : x ≤ (rootCeil q x)^q :=
  rootCeilGo_sound q x x (self_le_pow x hq)

theorem rootCeil_least (q x m : Nat) (hm : m < rootCeil q x) : m^q < x :=
  Nat.lt_of_not_le (rootCeilGo_least q x x m hm)

/-! ## §2 — `dyUp`: the dyadic upper reading of an exponent cut -/

/-- Dyadic upper numerator of the exponent cut `c` at denominator `2^j`,
    descending from the integer witness `B` (`c B 1 = true`): at each level
    take the odd midpoint exactly when the cut still affirms it. -/
def dyUp (c : Nat → Nat → Bool) (B : Nat) : Nat → Nat
  | 0 => B
  | j+1 => cond (c (2 * dyUp c B j - 1) (2^(j+1)))
                (2 * dyUp c B j - 1) (2 * dyUp c B j)

/-- ★ **Upper soundness**: the reading stays on the cut's `true` side — the
    only structural inputs are the integer witness and the forward doubling
    `c m k = true → c (2m) (2k) = true` (presentation rescale, the easy
    direction). -/
theorem dyUp_true (c : Nat → Nat → Bool) (B : Nat) (hB : c B 1 = true)
    (hdouble : ∀ m k, c m k = true → c (2*m) (2*k) = true) :
    ∀ j, c (dyUp c B j) (2^j) = true
  | 0 => hB
  | j+1 => by
      show c (cond (c (2 * dyUp c B j - 1) (2^(j+1)))
              (2 * dyUp c B j - 1) (2 * dyUp c B j)) (2^(j+1)) = true
      cases hcb : c (2 * dyUp c B j - 1) (2^(j+1)) with
      | true => exact hcb
      | false =>
        have h2 : c (2 * dyUp c B j) (2 * 2^j) = true :=
          hdouble _ _ (dyUp_true c B hB hdouble j)
        rw [show (2:Nat) * 2^j = 2^(j+1) from by rw [Nat.pow_succ, Nat.mul_comm]] at h2
        exact h2

/-! ## §3 — the composed schedule `powSched` -/

/-- ★★★ **The irrational-degree schedule**: `powSched c B k = ⌈k^{p/2^k}⌉` with
    `p = dyUp c B k` read off the exponent cut at precision `2^{-k}`.  Pure
    `ℕ`; every evaluation queries `c` — for a `CauchyCutSeq` limit, that query
    runs the exponent's modulus. -/
def powSched (c : Nat → Nat → Bool) (B k : Nat) : Nat :=
  rootCeil (2^k) (k ^ dyUp c B k)

/-- ★★ Soundness half of the ceiling spec: `k^p ≤ (powSched)^{2^k}`. -/
theorem powSched_sound (c : Nat → Nat → Bool) (B k : Nat) :
    k ^ dyUp c B k ≤ (powSched c B k)^(2^k) :=
  rootCeil_sound (2^k) _ (E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut.two_pow_pos k)

/-- ★★ Leastness half: anything below `powSched` falls short of `k^p`. -/
theorem powSched_least (c : Nat → Nat → Bool) (B k M : Nat) (hM : M < powSched c B k) :
    M^(2^k) < k ^ dyUp c B k :=
  rootCeil_least (2^k) _ M hM

/-! ## §4 — calibration: integer exponents return the polynomial ladder -/

/-- The rational-exponent cut `τ = s`: `decide (s·k ≤ m)`. -/
def ratCut (s : Nat) : Nat → Nat → Bool := fun m k => decide (s * k ≤ m)

theorem dyUp_rat (s : Nat) (hs : 1 ≤ s) : ∀ j, dyUp (ratCut s) s j = s * 2^j
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]; rfl
  | j+1 => by
      show cond (ratCut s (2 * dyUp (ratCut s) s j - 1) (2^(j+1))) _ _ = s * 2^(j+1)
      rw [dyUp_rat s hs j]
      have he : 2 * (s * 2^j) = s * 2^(j+1) := by
        rw [mul_left_comm 2 s (2^j), Nat.pow_succ, Nat.mul_comm (2^j) 2]
      have hpos : 1 ≤ s * 2^(j+1) := by
        have h1 : s * 1 ≤ s * 2^(j+1) :=
          Nat.mul_le_mul_left s
            (E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut.two_pow_pos (j+1))
        rw [Nat.mul_one] at h1
        exact Nat.le_trans hs h1
      have hfalse : ratCut s (2 * (s * 2^j) - 1) (2^(j+1)) = false := by
        apply decide_eq_false
        rw [he]
        intro hle
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (Nat.sub_lt hpos (by decide)))
      rw [hfalse]
      show 2 * (s * 2^j) = s * 2^(j+1)
      exact he

/-- ★★★ **Calibration**: at an integer exponent the composed schedule is
    exactly the polynomial one — `powSched (ratCut s) s k = k^s`.  The
    functional extends the integer ladder, it does not replace it. -/
theorem powSched_rat (s : Nat) (hs : 1 ≤ s) (k : Nat) :
    powSched (ratCut s) s k = k^s := by
  have hp : dyUp (ratCut s) s k = s * 2^k := dyUp_rat s hs k
  have hx : k ^ dyUp (ratCut s) s k = (k^s)^(2^k) := by
    rw [hp, pow_mul_pure k s (2^k)]
  -- k^s satisfies the bound, so rootCeil ≤ k^s; and nothing below it does.
  have hsound : k ^ dyUp (ratCut s) s k ≤ (powSched (ratCut s) s k)^(2^k) :=
    powSched_sound (ratCut s) s k
  have hub : ¬ (k^s < powSched (ratCut s) s k) := by
    intro hlt
    have := powSched_least (ratCut s) s k (k^s) hlt
    rw [hx] at this
    exact Nat.lt_irrefl _ this
  have hlb : ¬ (powSched (ratCut s) s k < k^s) := by
    intro hlt
    have hstrict : (powSched (ratCut s) s k)^(2^k) < (k^s)^(2^k) :=
      powBase_lt hlt (E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut.two_pow_pos k)
    rw [← hx] at hstrict
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hsound hstrict)
  exact Nat.le_antisymm (Nat.le_of_not_lt hub) (Nat.le_of_not_lt hlb)

/-! ## §5 — degree ∛2: the ladder eats its own degree-3 brick as an exponent -/

/-- Forward doubling for the ∛2 form cut — the easy multiplicative direction
    (`×8` on both cubes). -/
theorem cbrt2Cut_double (m k : Nat) (h : cbrt2Cut m k = true) :
    cbrt2Cut (2*m) (2*k) = true := by
  have hp : 2 * cube k ≤ cube m := of_decide_eq_true h
  apply decide_eq_true
  show 2 * cube (2*k) ≤ cube (2*m)
  rw [cube_double k, cube_double m, mul_left_comm 2 8 (cube k)]
  exact Nat.mul_le_mul_left 8 hp

/-- ★★ The dyadic reading of exponent ∛2 stays sound at every precision. -/
theorem cbrt_dyUp_true (j : Nat) : cbrt2Cut (dyUp cbrt2Cut 2 j) (2^j) = true :=
  dyUp_true cbrt2Cut 2 (by decide) cbrt2Cut_double j

/-- ★★★ **A schedule of degree ∛2, evaluated**: `powSched cbrt2Cut 2 2 = 3`
    — `dyUp` reads `∛2 ≤ 6/4` (and not `5/4`), and `⌈2^{6/4}⌉ = ⌈2√2⌉ = 3`.
    The first concretely computed irrational-degree schedule value. -/
theorem cbrtPow_at_two : powSched cbrt2Cut 2 2 = 3 := by decide

/-! ## §6 — degree e: the schedule runs e's constructed modulus -/

/-- e's limit cut, written through its modulus field: the layer index is
    *literally* `eulerCauchySeq.N m k` — evaluating this cut runs e's
    constructed modulus. -/
def eulerModCut : Nat → Nat → Bool := fun m k =>
  decide (eulerNum (eulerCauchySeq.N m k) * k ≤ eulerDen (eulerCauchySeq.N m k) * m)

/-- `eulerModCut` is pointwise e's completed limit cut. -/
theorem eulerModCut_eq_limit (m k : Nat) :
    eulerModCut m k = eulerCauchySeq.limit m k :=
  (E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut.eulerCut_eq
    (eulerCauchySeq.N m k) m k).symm

set_option maxRecDepth 8000 in
/-- ★★★ **A schedule of degree e, evaluated through e's modulus**:
    `powSched eulerModCut 3 2 = 7` — `dyUp` reads `e ≤ 11/4` (and not
    `5/2`), each query running `eulerCauchySeq.N`, and `⌈2^{11/4}⌉ = 7`.
    A modulus computed by calling another real's modulus: the receipt
    call-tree, witnessed by the kernel.  (`maxRecDepth` raised for the
    `rootCeilGo` descent from `2^11` — an elaborator budget, no axiom impact.) -/
theorem ePow_at_two : powSched eulerModCut 3 2 = 7 := by decide

/-! ## §7 — the cascade's first rung: e rescheduled through itself -/

/-- Weakening a `CauchyCutSeq`'s modulus to any pointwise-larger schedule. -/
def reschedule (T : CauchyCutSeq) (N' : Nat → Nat → Nat)
    (h : ∀ m k, T.N m k ≤ N' m k) : CauchyCutSeq where
  cs := T.cs
  N := N'
  cauchy := fun m k i j hi hj =>
    T.cauchy m k i j (Nat.le_trans (h m k) hi) (Nat.le_trans (h m k) hj)

/-- Rescheduling never moves the limit. -/
theorem reschedule_limit_eq (T : CauchyCutSeq) (N' : Nat → Nat → Nat)
    (h : ∀ m k, T.N m k ≤ N' m k) (m k : Nat) :
    (reschedule T N' h).limit m k = T.limit m k :=
  T.cauchy m k (N' m k) (T.N m k) (h m k) (Nat.le_refl _)

/-- ★★★ **e, self-scheduled**: e's cut sequence carrying the modulus
    `powSched eulerModCut 3 k + (k+2)` — a schedule that *queries e's own
    modulus* to bound e's own convergence.  Depth-1 of the operational
    cascade: the fold's receipt is written in terms of itself. -/
def eSelfScheduled : CauchyCutSeq :=
  reschedule eulerCauchySeq (fun _ k => powSched eulerModCut 3 k + (k+2))
    (fun _ k => Nat.le_add_left (k+2) _)

/-- The self-scheduled e is still e: the limit cut is unchanged. -/
theorem eSelfScheduled_limit_eq (m k : Nat) :
    eSelfScheduled.limit m k = eulerCauchySeq.limit m k :=
  reschedule_limit_eq eulerCauchySeq _ _ m k

/-! ## §8 — degree order transports to schedule order (the degree-as-cut backbone)

Exponent cuts are ordered by `τ₁ ≤ τ₂ ⟺ (τ₂'s true-set ⊆ τ₁'s)` (a larger real
affirms fewer probes).  The schedule functional is **monotone** along this
order: a larger degree never yields a smaller schedule.  This is what makes
"the degree of a real" a *cut-shaped* threshold over exponent cuts — the
predicate "a degree-τ schedule suffices for `x`" is monotone in τ, so its
threshold is a cut one level up.  (Whether that threshold is *decidable* is
exactly the effectivity question of the exact degree — Roth-grade content,
recorded on the frontier board, not claimed here.) -/

theorem pow_le_pow_exp {k : Nat} (hk : 1 ≤ k) {a b : Nat} (h : a ≤ b) :
    k^a ≤ k^b := by
  rw [← E213.Tactic.NatHelper.add_sub_of_le h, pow_add k a (b-a)]
  have h1 : k^a * 1 ≤ k^a * k^(b-a) := Nat.mul_le_mul_left _ (one_le_pow hk (b-a))
  rwa [Nat.mul_one] at h1

theorem rootCeil_mono (q : Nat) (hq : 1 ≤ q) {x₁ x₂ : Nat} (h : x₁ ≤ x₂) :
    rootCeil q x₁ ≤ rootCeil q x₂ := by
  refine Nat.le_of_not_lt (fun hlt => ?_)
  have hless : (rootCeil q x₂)^q < x₁ := rootCeil_least q x₁ _ hlt
  exact Nat.lt_irrefl _
    (Nat.lt_of_le_of_lt (Nat.le_trans h (rootCeil_sound q x₂ hq)) hless)

/-- ★★ **Degree order ⟹ dyadic-reading order**: if every probe `τ₂` affirms,
    `τ₁` affirms too (`τ₁ ≤ τ₂`), then the upper readings stay ordered at every
    precision. -/
theorem dyUp_mono (c₁ c₂ : Nat → Nat → Bool) (B : Nat)
    (hle : ∀ m k, c₂ m k = true → c₁ m k = true) :
    ∀ j, dyUp c₁ B j ≤ dyUp c₂ B j
  | 0 => Nat.le_refl B
  | j+1 => by
      have ih := dyUp_mono c₁ c₂ B hle j
      show (cond (c₁ (2 * dyUp c₁ B j - 1) (2^(j+1)))
              (2 * dyUp c₁ B j - 1) (2 * dyUp c₁ B j))
         ≤ (cond (c₂ (2 * dyUp c₂ B j - 1) (2^(j+1)))
              (2 * dyUp c₂ B j - 1) (2 * dyUp c₂ B j))
      have hLub : (cond (c₁ (2 * dyUp c₁ B j - 1) (2^(j+1)))
              (2 * dyUp c₁ B j - 1) (2 * dyUp c₁ B j)) ≤ 2 * dyUp c₁ B j := by
        cases c₁ (2 * dyUp c₁ B j - 1) (2^(j+1)) with
        | true => exact Nat.sub_le _ _
        | false => exact Nat.le_refl _
      cases hc2 : c₂ (2 * dyUp c₂ B j - 1) (2^(j+1)) with
      | false => exact Nat.le_trans hLub (Nat.mul_le_mul_left 2 ih)
      | true =>
        by_cases heq : dyUp c₁ B j = dyUp c₂ B j
        · rw [heq]
          cases hc1 : c₁ (2 * dyUp c₂ B j - 1) (2^(j+1)) with
          | true => exact Nat.le_refl _
          | false => rw [hle _ _ hc2] at hc1; exact absurd hc1 (by decide)
        · have hlt : dyUp c₁ B j < dyUp c₂ B j := Nat.lt_of_le_of_ne ih heq
          refine Nat.le_trans hLub (E213.Tactic.NatHelper.le_sub_of_add_le ?_)
          have h2 : 2 * (dyUp c₁ B j + 1) ≤ 2 * dyUp c₂ B j :=
            Nat.mul_le_mul_left 2 hlt
          rw [Nat.mul_add, Nat.mul_one] at h2
          exact Nat.le_trans (Nat.add_le_add_left (by decide) (2 * dyUp c₁ B j)) h2

/-- ★★★ **Degree order ⟹ schedule order**: the composed schedule is monotone
    in the exponent cut.  The backbone of "degree is a cut over exponent cuts":
    the threshold of "a degree-τ schedule suffices" is a monotone boundary. -/
theorem powSched_mono (c₁ c₂ : Nat → Nat → Bool) (B : Nat)
    (hle : ∀ m k, c₂ m k = true → c₁ m k = true) (k : Nat) :
    powSched c₁ B k ≤ powSched c₂ B k := by
  match k with
  | 0 => exact Nat.le_refl _
  | t+1 =>
    exact rootCeil_mono (2^(t+1))
      (E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut.two_pow_pos (t+1))
      (pow_le_pow_exp (Nat.succ_le_succ (Nat.zero_le t)) (dyUp_mono c₁ c₂ B hle (t+1)))

end E213.Lib.Math.NumberSystems.Real213.Modulus.ModulusComposition
