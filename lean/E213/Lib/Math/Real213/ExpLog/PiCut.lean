import E213.Lib.Math.Cauchy.Wallis
import E213.Lib.Math.Real213.AbCutSeq

/-!
# PiCut — π (and π/2) at the `Real213` cut level (an `AbCutSeq` instance)

Companion to `EulerCut`.  `Cauchy/Wallis.lean` builds π/2 at the **Raw /
`orderProj`** level via the Wallis product partial form `wallisNum n / wallisDen
n`, with the bracket π/2 ∈ (1, 2).  This file packages π/2 as an `AbCutSeq`
(`Real213/AbCutSeq.lean`) — inheriting the whole cut interface (each layer a
`ValidCut`+`RatioCut`, nesting, eventual constancy, completion to a `ValidCut`
limit) for free — and adds only the concrete **localization**, plus π itself by a
clean doubling.

  * `halfPiCut n := piHalfAb.cut n` (definitionally `constCut (wallisNum n)
    (wallisDen n)`);
  * **π/2 localized in (7/5, 2)** — `halfPiCut_at_2 = true` (π/2 ≤ 2),
    `halfPiCut_below_7_5 = false` for n ≥ 2 (π/2 > 7/5, since `W₂ = 64/45 > 7/5`
    exactly, by `decide` at n=2 + nesting — no need for the `omega`-laden
    axiom-dirty `wallis_sharper_lower`);
  * **π itself** — `piCut n m k := halfPiCut n m (2k)` (π ≤ m/k ⟺ π/2 ≤ m/2k), a
    `ValidCut`, localized in (14/5, 4).

The algebraic/transcendental split and completion-modulus-as-hypothesis story are
documented at `AbCutSeq`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Real213.ExpLog.PiCut

open E213.Lib.Math.Cauchy.WallisSeq
open E213.Lib.Math.Real213 (AbCutSeq)
open E213.Lib.Math.Real213.Core.ValidCut (ValidCut)

/-! ## §1 — π/2 as an `AbCutSeq` -/

/-- **π/2's Wallis-product sequence as an `AbCutSeq`** — ab-monotone
    (`wallis_isAbMonotonic`) with positive denominators (`wallis_isAbPositiveB`).
    The whole cut interface applies. -/
def piHalfAb : AbCutSeq := ⟨wallisRawSeq, wallis_isAbMonotonic, wallis_isAbPositiveB⟩

/-- **π/2's Wallis cut at layer `n`**: `decide (wallisNum n · k ≤ wallisDen n · m)`. -/
def halfPiCut (n : Nat) : Nat → Nat → Bool := piHalfAb.cut n

/-- Each π/2 cut is a `ValidCut` (from the generic structure). -/
theorem halfPiCut_valid (n : Nat) : ValidCut (halfPiCut n) := piHalfAb.cut_valid n

/-- The `constCut` view of `halfPiCut` — lets `Cauchy/Wallis`'s `orderProj`
    bounds transfer by `decide`/`rw`. -/
theorem halfPiCut_eq (n m k : Nat) :
    halfPiCut n m k = decide (wallisNum n * k ≤ wallisDen n * m) := by
  show E213.Lib.Math.Cauchy.Archimedean.orderProj m k
        (E213.Lens.Instances.AB.abLens.view (wallisRaw n).val) = _
  rw [wallisRaw_view]; rfl

/-- **Nesting** for π/2, from the generic `AbCutSeq.cut_false_fwd`. -/
theorem halfPiCut_false_fwd (m k N : Nat) (hN : halfPiCut N m k = false)
    (i : Nat) (hi : i ≥ N) : halfPiCut i m k = false :=
  piHalfAb.cut_false_fwd m k N hN i hi

/-! ## §2 — π/2 localized in the open interval `(7/5, 2)` -/

/-- ★★ **π/2 ≤ 2**: the cut at `2/1` is `true` at every layer (`wallis_upper_inv`). -/
theorem halfPiCut_at_2 (n : Nat) : halfPiCut n 2 1 = true := by
  rw [halfPiCut_eq]
  have := wallis_orderProj_above_2 2 1 (by decide) n
  rw [wallisRaw_view] at this; exact this

/-- ★★ **π/2 > 1**: the cut at `1/1` is `false` for n ≥ 1 (`wallis_lower_inv`). -/
theorem halfPiCut_below_1 (n : Nat) (hn : n ≥ 1) : halfPiCut n 1 1 = false := by
  rw [halfPiCut_eq]
  have := wallis_orderProj_below_1 1 1 (by decide) (by decide) n hn
  rw [wallisRaw_view] at this; exact this

/-- ★★★ **π/2 > 7/5**: the cut at `7/5` is `false` for n ≥ 2.  At n = 2 the Wallis
    value is `W₂ = 64/45 > 7/5` (`decide`: `64·5 = 320 > 315 = 45·7`), and nesting
    carries it forward — a *strict* sharp lower bound without the `omega`-laden
    (axiom-dirty) general `wallis_sharper_lower`. -/
theorem halfPiCut_below_7_5 (n : Nat) (hn : n ≥ 2) : halfPiCut n 7 5 = false :=
  halfPiCut_false_fwd 7 5 2 (by rw [halfPiCut_eq]; decide) n hn

/-- ★★★ **π/2 is strictly between 7/5 and 2, ∀ tail layer (n ≥ 2)**. -/
theorem halfPiCut_in_7_5_to_2 (n : Nat) (hn : n ≥ 2) :
    halfPiCut n 7 5 = false ∧ halfPiCut n 2 1 = true :=
  ⟨halfPiCut_below_7_5 n hn, halfPiCut_at_2 n⟩

/-! ## §3 — π itself (the doubling) localized in `(14/5, 4)` -/

/-- **π's cut at layer `n`**: `π ≤ m/k ⟺ π/2 ≤ m/2k`, so π's cut is the π/2 cut
    with the denominator doubled. -/
def piCut (n : Nat) : Nat → Nat → Bool := fun m k => halfPiCut n m (2 * k)

/-- ★ Each π cut is a `ValidCut`.  Doubling `k` preserves both monotonicities. -/
theorem piCut_valid (n : Nat) : ValidCut (piCut n) where
  upM := fun m1 m2 k hm h => (halfPiCut_valid n).upM m1 m2 (2*k) hm h
  dnK := fun m k1 k2 hk h =>
    (halfPiCut_valid n).dnK m (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) h

/-- ★★ **π ≤ 4**: the cut at `4/1` is `true` at every layer (π/2 ≤ 2 at `4/2`). -/
theorem piCut_at_4 (n : Nat) : piCut n 4 1 = true := by
  show halfPiCut n 4 2 = true
  rw [halfPiCut_eq]
  have := wallis_orderProj_above_2 4 2 (by decide) n
  rw [wallisRaw_view] at this; exact this

/-- ★★★ **π > 14/5**: the cut at `14/5` is `false` for n ≥ 2 (π/2 > 7/5 at the
    doubled threshold `14/10`). -/
theorem piCut_below_14_5 (n : Nat) (hn : n ≥ 2) : piCut n 14 5 = false :=
  halfPiCut_false_fwd 14 10 2 (by rw [halfPiCut_eq]; decide) n hn

/-- ★★★ **π is strictly between 14/5 and 4, ∀ tail layer (n ≥ 2)** — π ∈ (2.8, 4). -/
theorem piCut_in_14_5_to_4 (n : Nat) (hn : n ≥ 2) :
    piCut n 14 5 = false ∧ piCut n 4 1 = true :=
  ⟨piCut_below_14_5 n hn, piCut_at_4 n⟩

/-! ## §4 — Completion (modulus supplied) -/

/-- ★★★ **π/2's completed limit is a real (`ValidCut`)** — for any supplied
    modulus, from `AbCutSeq.toCauchy_limit_valid`. -/
theorem halfPiLimit_valid (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → piHalfAb.cut i m k = piHalfAb.cut j m k) :
    ValidCut (piHalfAb.toCauchy N hc).limit :=
  piHalfAb.toCauchy_limit_valid N hc

/-- ★★★ **The completed limit inherits the localization** — `false` at `7/5`,
    `true` at `2/1`, provided the modulus reached the `n ≥ 2` regime at `7/5`. -/
theorem halfPiLimit_in_7_5_to_2 (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → piHalfAb.cut i m k = piHalfAb.cut j m k)
    (h75 : N 7 5 ≥ 2) :
    (piHalfAb.toCauchy N hc).limit 7 5 = false
    ∧ (piHalfAb.toCauchy N hc).limit 2 1 = true :=
  piHalfAb.limit_brackets N hc 7 5 2 1 2
    (fun n hn => halfPiCut_below_7_5 n hn) (fun n => halfPiCut_at_2 n) h75

end E213.Lib.Math.Real213.ExpLog.PiCut
