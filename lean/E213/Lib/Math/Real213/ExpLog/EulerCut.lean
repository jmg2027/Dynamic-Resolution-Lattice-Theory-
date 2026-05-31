import E213.Lib.Math.Cauchy.Euler
import E213.Lib.Math.Cauchy.MonotonicBounded
import E213.Lib.Math.Real213.Core.ValidCut
import E213.Lib.Math.Analysis.CauchyCompleteValid

/-!
# EulerCut — e at the `Real213` cut level: nested `ValidCut`s, localized, irrational

`Cauchy/Euler.lean` builds e at the **Raw / `orderProj`** level: the partial sums
`eulerNum n / eulerDen n = Σ_{j≤n} 1/j!`, the bracket `e ∈ (2,3)`, the sharper
`e > 8/3`, and the irrationality discrimination `e ≠ a/b`.  This file lifts that
to the `Real213` **`ValidCut`** level and connects it to the general completeness
machinery (`Analysis/CauchyCompleteValid`).

## What e gets, PURE

  * **a nested sequence of rational `ValidCut`s** — `eulerCut n := constCut
    (eulerNum n) (eulerDen n)`, each a `ValidCut` *and* a `RatioCut`
    (`constCut_valid` / `constCut_ratio`), and **nested**: a `false` reading
    propagates forward (`eulerCut_false_fwd`, the monotone-chain engine
    `orderProj_false_propagates`).
  * **localization in the open interval `(8/3, 3)`** — `eulerCut_at_3 = true`
    (e ≤ 3), `eulerCut_below_8_3 = false` for n ≥ 4 (e > 8/3), `eulerCut_below_2
    = false` (e > 2).  Strictly between two rationals, ∀ tail.
  * **irrationality** — `Cauchy/Euler.e_neq_a_third` etc. (cited, not re-proved).
  * **per-threshold completion** — at any `(m,k)` with a `false`-witness `N₀`, the
    cut is eventually constant (`eulerCut_eventually_const`); packaged as a
    `CauchyCutSeq` whose `limit` is a `ValidCut` via this session's
    `CauchyCutSeq.limit_valid`.

## What e does *not* get — and why (the algebraic/transcendental split)

φ (`PhiCauchyLimit`) assembles into a `CauchyCutSeq` **unconditionally**: its
convergent cut stabilizes *exactly* with the closed-form modulus `N(m,k) = 2k`
(`cs_eq_phiCut`), because φ is algebraic — a fixed point with a decidable
closed-form cut (`phiCut`).  e has no such closed form: a **total** modulus
`N(m,k)` covering *every* `(m,k)` would have to decide, at each rational
threshold, whether `e ≤ m/k` or `e > m/k` — i.e. the global order-Cauchy closure,
which `Cauchy/MonotonicBounded` (§180–194) **deliberately refuses** as a smuggled
LEM (mirroring ZFC's power-set commitment).  So `EulerCutSeq` below takes the
modulus as a **hypothesis**: the completeness machinery applies the moment a
modulus is supplied, and the structural barrier is *exactly* that modulus — not a
gap in the cut construction.  This is the honest 213 shape for a transcendental.

All ∅-axiom.
-/

namespace E213.Lib.Math.Real213.ExpLog.EulerCut

open E213.Lib.Math.Cauchy.EulerSeq
open E213.Lib.Math.Cauchy.EulerSharperPure (euler_sharper_8_3_pure)
open E213.Lib.Math.Cauchy.MonotonicBounded
open E213.Lib.Math.Cauchy.Archimedean (orderProj)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Core.ValidCut
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-! ## §1 — e's partial-sum cut as a nested `ValidCut` sequence -/

/-- **e's partial-sum cut at layer `n`**: the rational `Σ_{j≤n} 1/j!
    = eulerNum n / eulerDen n` read as a Cut, `decide (eulerNum n · k ≤
    eulerDen n · m)`. -/
def eulerCut (n : Nat) : Nat → Nat → Bool := constCut (eulerNum n) (eulerDen n)

/-- ★ Each partial-sum cut is a `ValidCut` (monotone in `m`, antitone in `k`). -/
theorem eulerCut_valid (n : Nat) : ValidCut (eulerCut n) := constCut_valid _ _

/-- ★ Each partial-sum cut is a `RatioCut` (respects rational ordering). -/
theorem eulerCut_ratio (n : Nat) : RatioCut (eulerCut n) := constCut_ratio _ _

/-- The `Raw`/`orderProj` reading of the Euler sequence is *definitionally* the
    `constCut` reading — the bridge between `Cauchy/Euler` and this file. -/
theorem orderProj_eq_eulerCut (n m k : Nat) :
    orderProj m k (abLens.view (eulerRawSeq n)) = eulerCut n m k := by
  show orderProj m k (abLens.view (eulerRaw n).val) = eulerCut n m k
  rw [eulerRaw_view]; rfl

/-- ★★ **Nesting**: a `false` reading at layer `N` persists at every later layer.
    The partial sums climb toward e, so once `S_N > m/k` the tail stays above
    `m/k`.  Transports the monotone-chain engine `orderProj_false_propagates`. -/
theorem eulerCut_false_fwd (m k N : Nat) (hN : eulerCut N m k = false)
    (i : Nat) (hi : i ≥ N) : eulerCut i m k = false := by
  have hraw : orderProj m k (abLens.view (eulerRawSeq N)) = false := by
    rw [orderProj_eq_eulerCut]; exact hN
  have h := orderProj_false_propagates eulerRawSeq euler_isAbMonotonic
    euler_isAbPositiveB m k N hraw i hi
  rw [orderProj_eq_eulerCut] at h
  exact h

/-! ## §2 — e localized in the open interval `(8/3, 3)` -/

/-- ★★ **e ≤ 3**: the cut at `3/1` is `true` at every layer (`euler_upper_inv`:
    `eulerNum ≤ 3·eulerDen − 1`). -/
theorem eulerCut_at_3 (n : Nat) : eulerCut n 3 1 = true := by
  have := euler_orderProj_above_3 3 1 (by decide) n
  rw [eulerRaw_view] at this; exact this

/-- ★★ **e > 2**: the cut at `2/1` is `false` for n ≥ 2 (`euler_lower_inv`:
    `eulerNum ≥ 2·eulerDen + 1`). -/
theorem eulerCut_below_2 (n : Nat) (hn : n ≥ 2) : eulerCut n 2 1 = false := by
  have := euler_orderProj_below_2 2 1 (by decide) (by decide) n hn
  rw [eulerRaw_view] at this; exact this

/-- ★★★ **e > 8/3**: the cut at `8/3` is `false` for n ≥ 4 — the sharp lower
    bound (`euler_sharper_8_3_pure`: `3·eulerNum ≥ 8·eulerDen + 1`).  Combined
    with `eulerCut_at_3`, this pins e strictly inside `(8/3, 3)`. -/
theorem eulerCut_below_8_3 (n : Nat) (hn : n ≥ 4) : eulerCut n 8 3 = false := by
  show decide (eulerNum n * 3 ≤ eulerDen n * 8) = false
  apply decide_eq_false
  intro hle
  have h := euler_sharper_8_3_pure n hn
  rw [Nat.mul_comm (eulerNum n) 3, Nat.mul_comm (eulerDen n) 8] at hle
  exact absurd (Nat.le_trans h hle) (Nat.not_succ_le_self _)

/-- ★★★ **e is strictly between 8/3 and 3, ∀ tail layer (n ≥ 4)**: the cut reads
    `false` at `8/3` and `true` at `3/1`.  The localization bundle. -/
theorem eulerCut_in_8_3_to_3 (n : Nat) (hn : n ≥ 4) :
    eulerCut n 8 3 = false ∧ eulerCut n 3 1 = true :=
  ⟨eulerCut_below_8_3 n hn, eulerCut_at_3 n⟩

/-! ## §3 — Per-threshold completion via the general machinery -/

/-- ★★ **Eventual constancy at a `false`-witnessed threshold**: if `eulerCut N₀
    m k = false`, then beyond `N₀` the cut is constant at `(m,k)`.  This is the
    per-`(m,k)` order-Cauchy property — exactly the field a `CauchyCutSeq` needs,
    once a modulus is supplied. -/
theorem eulerCut_eventually_const (m k N₀ : Nat) (hN₀ : eulerCut N₀ m k = false) :
    ∀ i j, i ≥ N₀ → j ≥ N₀ → eulerCut i m k = eulerCut j m k := by
  intro i j hi hj
  rw [eulerCut_false_fwd m k N₀ hN₀ i hi, eulerCut_false_fwd m k N₀ hN₀ j hj]

/-- **e as a `CauchyCutSeq`, modulo a supplied modulus.**  Given any modulus
    function `N` that witnesses the order-Cauchy property of `eulerCut` (e.g.
    assembled from `false`-witnesses per threshold), the partial-sum cut sequence
    *is* a `CauchyCutSeq`.  The transcendentality of e lives entirely in the
    hypothesis `hcauchy`: no closed form supplies it for all `(m,k)` (see the
    module note), but the moment it is given, completion proceeds. -/
def eulerCutSeq (N : Nat → Nat → Nat)
    (hcauchy : ∀ m k i j, i ≥ N m k → j ≥ N m k → eulerCut i m k = eulerCut j m k) :
    CauchyCutSeq where
  cs := eulerCut
  N := N
  cauchy := hcauchy

/-- ★★★ **e's completed limit is a real (`ValidCut`).**  For any supplied modulus,
    the Cauchy limit of the partial-sum cuts is a `ValidCut` — directly from this
    session's general completeness `CauchyCutSeq.limit_valid`, since every term
    `eulerCut n` is valid.  e is a bona fide `Real213` cut wherever it is
    completed. -/
theorem eulerCutSeq_limit_valid (N : Nat → Nat → Nat)
    (hcauchy : ∀ m k i j, i ≥ N m k → j ≥ N m k → eulerCut i m k = eulerCut j m k) :
    ValidCut (eulerCutSeq N hcauchy).limit :=
  (eulerCutSeq N hcauchy).limit_valid (fun i => eulerCut_valid i)

/-- ★★★ **The completed limit inherits the localization**: it reads `false` at
    `8/3` and `true` at `3/1`, provided the supplied modulus has reached the
    `n ≥ 4` regime there (`N 8 3 ≥ 4`).  e's limit sits in `(8/3, 3)` as a real
    cut, not merely the approximants. -/
theorem eulerCutSeq_limit_in_8_3_to_3 (N : Nat → Nat → Nat)
    (hcauchy : ∀ m k i j, i ≥ N m k → j ≥ N m k → eulerCut i m k = eulerCut j m k)
    (h83 : N 8 3 ≥ 4) :
    (eulerCutSeq N hcauchy).limit 8 3 = false
    ∧ (eulerCutSeq N hcauchy).limit 3 1 = true := by
  constructor
  · -- limit at (8,3) = cs (N 8 3) 8 3 = eulerCut (N 8 3) 8 3 = false
    show eulerCut (N 8 3) 8 3 = false
    exact eulerCut_below_8_3 (N 8 3) h83
  · show eulerCut (N 3 1) 3 1 = true
    exact eulerCut_at_3 (N 3 1)

end E213.Lib.Math.Real213.ExpLog.EulerCut
