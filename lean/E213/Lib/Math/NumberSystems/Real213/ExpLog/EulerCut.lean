import E213.Lib.Math.Analysis.Cauchy.Euler
import E213.Lib.Math.NumberSystems.Real213.AbCutSeq

/-!
# EulerCut — e at the `Real213` cut level (an `AbCutSeq` instance)

`Cauchy/Euler.lean` builds e at the **Raw / `orderProj`** level: the partial sums
`eulerNum n / eulerDen n = Σ_{j≤n} 1/j!`, the bracket `e ∈ (2,3)`, the sharper
`e > 8/3`, and the irrationality discrimination `e ≠ a/b`.  This file packages e
as an `AbCutSeq` (`Real213/AbCutSeq.lean`) — so the whole cut interface (each
layer a `ValidCut`+`RatioCut`, nesting, eventual constancy, completion to a
`ValidCut` limit) comes **for free** from the generic structure — and adds only
e's concrete **localization**:

  * `eulerCut n := eAb.cut n` (definitionally `constCut (eulerNum n) (eulerDen n)`);
  * **localized in (8/3, 3)** — `eulerCut_at_3 = true` (e ≤ 3),
    `eulerCut_below_8_3 = false` for n ≥ 4 (e > 8/3, the sharp bound),
    `eulerCut_below_2 = false` (e > 2);
  * irrationality lives in `Cauchy/Euler.e_neq_a_third` etc. (cited, not re-proved).

The algebraic/transcendental split and the completion-modulus-as-hypothesis story
are documented at `AbCutSeq`; e supplies no closed-form total modulus (a total one
would be the global order-Cauchy closure `Cauchy/MonotonicBounded` §180–194
refuses as smuggled LEM).

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut

open E213.Lib.Math.Analysis.Cauchy.EulerSeq
open E213.Lib.Math.Analysis.Cauchy.EulerSharperPure (euler_sharper_8_3_pure)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)

/-! ## §1 — e as an `AbCutSeq` -/

/-- **e's partial-sum sequence as an `AbCutSeq`** — `Σ_{j≤n} 1/j!`, ab-monotone
    (`euler_isAbMonotonic`) with positive denominators (`euler_isAbPositiveB`).
    The whole cut interface (`AbCutSeq.cut_valid` / `cut_ratio` / `cut_false_fwd`
    / `cut_eventually_const` / `toCauchy_limit_valid`) applies. -/
def eAb : AbCutSeq := ⟨eulerRawSeq, euler_isAbMonotonic, euler_isAbPositiveB⟩

/-- **e's partial-sum cut at layer `n`**: `decide (eulerNum n · k ≤ eulerDen n · m)`.
    The layer-n rational `eulerNum n / eulerDen n` read as a Cut. -/
def eulerCut (n : Nat) : Nat → Nat → Bool := eAb.cut n

/-- Each partial-sum cut is a `ValidCut` (from the generic structure). -/
theorem eulerCut_valid (n : Nat) : ValidCut (eulerCut n) := eAb.cut_valid n

/-- The `constCut` view of `eulerCut` — `eulerCut n = constCut (eulerNum n)
    (eulerDen n)` — via `eulerRaw_view` (the `Raw` reading is the `(num, den)`
    pair).  Lets `Cauchy/Euler`'s `orderProj` bounds transfer by `decide`/`rw`. -/
theorem eulerCut_eq (n m k : Nat) :
    eulerCut n m k = decide (eulerNum n * k ≤ eulerDen n * m) := by
  show E213.Lib.Math.Analysis.Cauchy.Archimedean.orderProj m k
        (E213.Lens.Instances.AB.abLens.view (eulerRaw n).val) = _
  rw [eulerRaw_view]; rfl

/-! ## §2 — e localized in the open interval `(8/3, 3)` -/

/-- ★★ **e ≤ 3**: the cut at `3/1` is `true` at every layer (`euler_upper_inv`). -/
theorem eulerCut_at_3 (n : Nat) : eulerCut n 3 1 = true := by
  rw [eulerCut_eq]
  have := euler_orderProj_above_3 3 1 (by decide) n
  rw [eulerRaw_view] at this; exact this

/-- ★★ **e > 2**: the cut at `2/1` is `false` for n ≥ 2 (`euler_lower_inv`). -/
theorem eulerCut_below_2 (n : Nat) (hn : n ≥ 2) : eulerCut n 2 1 = false := by
  rw [eulerCut_eq]
  have := euler_orderProj_below_2 2 1 (by decide) (by decide) n hn
  rw [eulerRaw_view] at this; exact this

/-- ★★★ **e > 8/3**: the cut at `8/3` is `false` for n ≥ 4 — the sharp lower
    bound (`euler_sharper_8_3_pure`: `3·eulerNum ≥ 8·eulerDen + 1`). -/
theorem eulerCut_below_8_3 (n : Nat) (hn : n ≥ 4) : eulerCut n 8 3 = false := by
  rw [eulerCut_eq]
  apply decide_eq_false
  intro hle
  have h := euler_sharper_8_3_pure n hn
  rw [Nat.mul_comm (eulerNum n) 3, Nat.mul_comm (eulerDen n) 8] at hle
  exact absurd (Nat.le_trans h hle) (Nat.not_succ_le_self _)

/-- ★★★ **e is strictly between 8/3 and 3, ∀ tail layer (n ≥ 4)**. -/
theorem eulerCut_in_8_3_to_3 (n : Nat) (hn : n ≥ 4) :
    eulerCut n 8 3 = false ∧ eulerCut n 3 1 = true :=
  ⟨eulerCut_below_8_3 n hn, eulerCut_at_3 n⟩

/-! ## §3 — Completion (modulus supplied) -/

/-- ★★★ **e's completed limit is a real (`ValidCut`)** — for any supplied modulus
    witnessing the order-Cauchy property, directly from `AbCutSeq.toCauchy_limit_valid`. -/
theorem eulerLimit_valid (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → eAb.cut i m k = eAb.cut j m k) :
    ValidCut (eAb.toCauchy N hc).limit :=
  eAb.toCauchy_limit_valid N hc

/-- ★★★ **The completed limit inherits the localization**: `false` at `8/3`,
    `true` at `3/1`, provided the supplied modulus reached the `n ≥ 4` regime at
    `8/3` (`N 8 3 ≥ 4`).  e's limit sits in `(8/3, 3)` as a real cut. -/
theorem eulerLimit_in_8_3_to_3 (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → eAb.cut i m k = eAb.cut j m k)
    (h83 : N 8 3 ≥ 4) :
    (eAb.toCauchy N hc).limit 8 3 = false
    ∧ (eAb.toCauchy N hc).limit 3 1 = true :=
  eAb.limit_brackets N hc 8 3 3 1 4
    (fun n hn => eulerCut_below_8_3 n hn) (fun n => eulerCut_at_3 n) h83

end E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut
