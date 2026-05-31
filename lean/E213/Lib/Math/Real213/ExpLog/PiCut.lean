import E213.Lib.Math.Cauchy.Wallis
import E213.Lib.Math.Cauchy.MonotonicBounded
import E213.Lib.Math.Real213.Core.ValidCut
import E213.Lib.Math.Analysis.CauchyCompleteValid

/-!
# PiCut — π (and π/2) at the `Real213` cut level: nested `ValidCut`s, localized

Companion to `EulerCut`.  `Cauchy/Wallis.lean` builds π/2 at the **Raw /
`orderProj`** level via the Wallis product partial form `wallisNum n / wallisDen
n`, with the bracket π/2 ∈ (1, 2).  This file lifts π/2 — and, by a clean
doubling, π itself — to the `Real213` **`ValidCut`** level and wires it to the
general completeness machinery (`Analysis/CauchyCompleteValid`).

## What π gets, PURE

  * **π/2 as a nested rational `ValidCut` sequence** — `halfPiCut n := constCut
    (wallisNum n) (wallisDen n)`, each a `ValidCut` *and* a `RatioCut`, and
    **nested** (`halfPiCut_false_fwd`, the monotone-chain engine).
  * **π/2 localized in `(7/5, 2)`** — `halfPiCut_at_2 = true` (π/2 ≤ 2),
    `halfPiCut_below_7_5 = false` for n ≥ 2 (π/2 > 7/5, since `W₂ = 64/45 >
    7/5` exactly, by `decide` + nesting — no need for the `omega`-laden general
    `wallis_sharper_lower`).
  * **π itself** — `piCut n m k := halfPiCut n m (2k)` (the cut "π ≤ m/k" ⟺ "π/2 ≤
    m/2k"), again a `ValidCut`, localized in `(14/5, 4)` (`piCut_below_14_5`,
    `piCut_at_4`).
  * **per-threshold completion** — eventual constancy at any `false`-witnessed
    `(m,k)` (`halfPiCut_eventually_const`), packaged as a `CauchyCutSeq` whose
    `limit` is a `ValidCut` via this session's `CauchyCutSeq.limit_valid`.

## The algebraic/transcendental split (same as `EulerCut`)

Like e, π is transcendental: there is no closed-form total cut.  A **total**
modulus `N(m,k)` for *every* threshold is the global order-Cauchy closure that
`Cauchy/MonotonicBounded` (§180–194) **refuses** as a smuggled LEM.  So
`halfPiCutSeq` takes the modulus as a **hypothesis** — completion proceeds the
moment one is supplied, and the barrier is exactly that modulus, not the cut.
Contrast algebraic φ (`PhiCauchyLimit`), whose closed-form modulus `N = 2k` makes
the `CauchyCutSeq` unconditional.

All ∅-axiom.
-/

namespace E213.Lib.Math.Real213.ExpLog.PiCut

open E213.Lib.Math.Cauchy.WallisSeq
open E213.Lib.Math.Cauchy.MonotonicBounded
open E213.Lib.Math.Cauchy.Archimedean (orderProj)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Core.ValidCut
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-! ## §1 — π/2's Wallis cut as a nested `ValidCut` sequence -/

/-- **π/2's Wallis cut at layer `n`**: the rational Wallis partial product
    `wallisNum n / wallisDen n` read as a Cut, `decide (wallisNum n · k ≤
    wallisDen n · m)`. -/
def halfPiCut (n : Nat) : Nat → Nat → Bool := constCut (wallisNum n) (wallisDen n)

/-- ★ Each π/2 cut is a `ValidCut`. -/
theorem halfPiCut_valid (n : Nat) : ValidCut (halfPiCut n) := constCut_valid _ _

/-- ★ Each π/2 cut is a `RatioCut`. -/
theorem halfPiCut_ratio (n : Nat) : RatioCut (halfPiCut n) := constCut_ratio _ _

/-- The `Raw`/`orderProj` reading of the Wallis sequence is *definitionally* the
    `constCut` reading — the bridge between `Cauchy/Wallis` and this file. -/
theorem orderProj_eq_halfPiCut (n m k : Nat) :
    orderProj m k (abLens.view (wallisRawSeq n)) = halfPiCut n m k := by
  show orderProj m k (abLens.view (wallisRaw n).val) = halfPiCut n m k
  rw [wallisRaw_view]; rfl

/-- ★★ **Nesting**: a `false` reading at layer `N` persists at every later layer.
    The Wallis partial products climb toward π/2.  Transports
    `orderProj_false_propagates`. -/
theorem halfPiCut_false_fwd (m k N : Nat) (hN : halfPiCut N m k = false)
    (i : Nat) (hi : i ≥ N) : halfPiCut i m k = false := by
  have hraw : orderProj m k (abLens.view (wallisRawSeq N)) = false := by
    rw [orderProj_eq_halfPiCut]; exact hN
  have h := orderProj_false_propagates wallisRawSeq wallis_isAbMonotonic
    wallis_isAbPositiveB m k N hraw i hi
  rw [orderProj_eq_halfPiCut] at h
  exact h

/-! ## §2 — π/2 localized in the open interval `(7/5, 2)` -/

/-- ★★ **π/2 ≤ 2**: the cut at `2/1` is `true` at every layer
    (`wallis_upper_inv`). -/
theorem halfPiCut_at_2 (n : Nat) : halfPiCut n 2 1 = true := by
  have := wallis_orderProj_above_2 2 1 (by decide) n
  rw [wallisRaw_view] at this; exact this

/-- ★★ **π/2 > 1**: the cut at `1/1` is `false` for n ≥ 1 (`wallis_lower_inv`). -/
theorem halfPiCut_below_1 (n : Nat) (hn : n ≥ 1) : halfPiCut n 1 1 = false := by
  have := wallis_orderProj_below_1 1 1 (by decide) (by decide) n hn
  rw [wallisRaw_view] at this; exact this

/-- ★★★ **π/2 > 7/5**: the cut at `7/5` is `false` for n ≥ 2.  At n = 2 the Wallis
    value is exactly `W₂ = 64/45 > 7/5` (`decide`: `64·5 = 320 > 315 = 45·7`),
    and nesting carries it to every later layer — a *strict* sharp lower bound
    obtained without the `omega`-laden (axiom-dirty) general `wallis_sharper_lower`. -/
theorem halfPiCut_below_7_5 (n : Nat) (hn : n ≥ 2) : halfPiCut n 7 5 = false :=
  halfPiCut_false_fwd 7 5 2 (by decide) n hn

/-- ★★★ **π/2 is strictly between 7/5 and 2, ∀ tail layer (n ≥ 2)**. -/
theorem halfPiCut_in_7_5_to_2 (n : Nat) (hn : n ≥ 2) :
    halfPiCut n 7 5 = false ∧ halfPiCut n 2 1 = true :=
  ⟨halfPiCut_below_7_5 n hn, halfPiCut_at_2 n⟩

/-! ## §3 — π itself (the doubling) localized in `(14/5, 4)` -/

/-- **π's cut at layer `n`**: `π ≤ m/k ⟺ π/2 ≤ m/2k`, so π's cut is the π/2 cut
    with the denominator doubled — `halfPiCut n m (2k)`. -/
def piCut (n : Nat) : Nat → Nat → Bool := fun m k => halfPiCut n m (2 * k)

/-- ★ Each π cut is a `ValidCut`.  Doubling `k` preserves both monotonicities
    (`2·k₁ ≤ 2·k₂` from `k₁ ≤ k₂`). -/
theorem piCut_valid (n : Nat) : ValidCut (piCut n) where
  upM := fun m1 m2 k hm h => (halfPiCut_valid n).upM m1 m2 (2*k) hm h
  dnK := fun m k1 k2 hk h =>
    (halfPiCut_valid n).dnK m (2*k1) (2*k2) (Nat.mul_le_mul_left 2 hk) h

/-- ★★ **π ≤ 4**: the cut at `4/1` is `true` at every layer (π/2 ≤ 2 at `4/2`). -/
theorem piCut_at_4 (n : Nat) : piCut n 4 1 = true := by
  show halfPiCut n 4 2 = true
  have := wallis_orderProj_above_2 4 2 (by decide) n
  rw [wallisRaw_view] at this; exact this

/-- ★★★ **π > 14/5**: the cut at `14/5` is `false` for n ≥ 2 (π/2 > 7/5 at the
    doubled threshold `14/10`; `decide` at n=2 + nesting). -/
theorem piCut_below_14_5 (n : Nat) (hn : n ≥ 2) : piCut n 14 5 = false :=
  halfPiCut_false_fwd 14 10 2 (by decide) n hn

/-- ★★★ **π is strictly between 14/5 and 4, ∀ tail layer (n ≥ 2)** — i.e.
    π ∈ (2.8, 4) as a nested rational cut. -/
theorem piCut_in_14_5_to_4 (n : Nat) (hn : n ≥ 2) :
    piCut n 14 5 = false ∧ piCut n 4 1 = true :=
  ⟨piCut_below_14_5 n hn, piCut_at_4 n⟩

/-! ## §4 — Per-threshold completion via the general machinery -/

/-- ★★ **Eventual constancy at a `false`-witnessed threshold** for π/2. -/
theorem halfPiCut_eventually_const (m k N₀ : Nat) (hN₀ : halfPiCut N₀ m k = false) :
    ∀ i j, i ≥ N₀ → j ≥ N₀ → halfPiCut i m k = halfPiCut j m k := by
  intro i j hi hj
  rw [halfPiCut_false_fwd m k N₀ hN₀ i hi, halfPiCut_false_fwd m k N₀ hN₀ j hj]

/-- **π/2 as a `CauchyCutSeq`, modulo a supplied modulus.**  The transcendentality
    lives in the hypothesis `hcauchy`; once a modulus is given, completion
    proceeds (see the module note on the algebraic/transcendental split). -/
def halfPiCutSeq (N : Nat → Nat → Nat)
    (hcauchy : ∀ m k i j, i ≥ N m k → j ≥ N m k → halfPiCut i m k = halfPiCut j m k) :
    CauchyCutSeq where
  cs := halfPiCut
  N := N
  cauchy := hcauchy

/-- ★★★ **π/2's completed limit is a real (`ValidCut`).**  Directly from this
    session's `CauchyCutSeq.limit_valid`, since every term `halfPiCut n` is valid. -/
theorem halfPiCutSeq_limit_valid (N : Nat → Nat → Nat)
    (hcauchy : ∀ m k i j, i ≥ N m k → j ≥ N m k → halfPiCut i m k = halfPiCut j m k) :
    ValidCut (halfPiCutSeq N hcauchy).limit :=
  (halfPiCutSeq N hcauchy).limit_valid (fun i => halfPiCut_valid i)

/-- ★★★ **The completed limit inherits the localization** — `false` at `7/5`,
    `true` at `2/1`, provided the supplied modulus reached the `n ≥ 2` regime at
    `7/5` (`N 7 5 ≥ 2`).  π/2's limit sits in `(7/5, 2)` as a real cut. -/
theorem halfPiCutSeq_limit_in_7_5_to_2 (N : Nat → Nat → Nat)
    (hcauchy : ∀ m k i j, i ≥ N m k → j ≥ N m k → halfPiCut i m k = halfPiCut j m k)
    (h75 : N 7 5 ≥ 2) :
    (halfPiCutSeq N hcauchy).limit 7 5 = false
    ∧ (halfPiCutSeq N hcauchy).limit 2 1 = true := by
  constructor
  · show halfPiCut (N 7 5) 7 5 = false
    exact halfPiCut_below_7_5 (N 7 5) h75
  · show halfPiCut (N 2 1) 2 1 = true
    exact halfPiCut_at_2 (N 2 1)

end E213.Lib.Math.Real213.ExpLog.PiCut
