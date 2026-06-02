import E213.Lib.Math.Real213.ContinuedFractionFloor
import E213.Lib.Math.Cauchy.DivergenceDepth
import E213.Lib.Math.Cauchy.DepthPiQuartic
import E213.Lib.Math.Cauchy.DepthCoordGenerator

/-!
# SpiralLayer — the divergence-depth layer is an intensional coordinate

A finer classification of reals than algebraic / transcendental: the **divergence
depth** (number of cross-determinant → ratio → finite-difference lifts to a constant
floor).  This file pins two honest facts about that coordinate.

  * ★★★ `depth_is_intensional` — the depth is an invariant of the chosen *holonomic
    presentation*, not of the bare real.  In the **regular continued fraction** the
    cross-determinant is universally on the `±1` floor (`cf_det_sq`, `W² = 1` for every
    partial-quotient sequence) — so the regular CF collapses **every** real to depth 1.
    The depths 3 (e) and 6 (π) live in the *series* presentations: e's factorial-series
    ratio has a vanishing second difference (`depth_three`, depth `3`), π's Wallis-product
    ratio is a degree-4 polynomial (`piRatio_polyDepth`, depth `6 = 2 + 4`).  Same real,
    different presentation, different layer — the layer is intensional (cf.
    `Real213.IntensionalCompletability`: completability is intensional, the cut is the
    gauge-invariant).
  * ★★ `depth_spectrum_unrestricted` — every finite depth `d` is realized *exactly* by an
    explicit sequence (`genExp_depth_exact`).  So the depth spectrum is all of `ℕ` (∪ `∞`),
    not a privileged subset: the values `{1, 3, 6}` of `{φ, e, π}` are a selection of three
    constants (ratio-degrees `{0, 1, 4}`), not a structural law.

Positioning (not formalised here; classical): the depth is **orthogonal to the
Mahler/Koksma/irrationality-measure hierarchy** — those put e and π in the same class
(both `S`, both `μ = 2`) and cannot separate them; the depth (e `3` < π `6`) tracks the
*continued-fraction holonomicity* axis, the one classical distinction that does separate
e (patterned CF) from π (irregular CF, conjecturally non-holonomic).  "Rate-carrying vs
rate-free" is "holonomic CF vs non-holonomic CF"; the non-holonomicity of π's partial
quotients is observed, not proved.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.SpiralLayer

open E213.Lib.Math.Real213.ContinuedFractionFloor (cfDet cf_det_sq)
open E213.Lib.Math.Cauchy.DivergenceDepth (ratio depth_three)
open E213.Lib.Math.Cauchy.DepthPiQuartic (piRatio piRatio_polyDepth)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Cauchy.DepthCoordGenerator (genExp genExp_depth_exact)

/-- ★★★ **The divergence-depth layer is intensional.**  The regular continued fraction
    collapses every real to the depth-1 det-one floor (`W² = 1`, universal); the depths
    `3` (e) and `6` (π) are resolved only by the series presentations.  Depth classifies
    the holonomic presentation, not the bare real. -/
theorem depth_is_intensional :
    -- regular CF: the universal depth-1 floor (every real, every partial-quotient sequence)
    (∀ (a : Nat → Nat) (n : Nat), cfDet a n * cfDet a n = 1)
    -- e's factorial series: depth 3 (the ratio's second difference vanishes)
    ∧ (∀ n, ratio (n+2) - ratio (n+1) = ratio (n+1) - ratio n)
    -- π's Wallis series: the ratio is a degree-4 polynomial (depth 6 = 2 + 4)
    ∧ polyDepth 4 piRatio :=
  ⟨cf_det_sq, depth_three, piRatio_polyDepth⟩

/-- ★★ **The depth spectrum is unrestricted.**  Every finite depth `d` is realized
    *exactly* by the binomial-column generator `genExp d` — depth `d` and not below.  So
    the spectrum is all of `ℕ`; `{1, 3, 6}` for `{φ, e, π}` is a selection (ratio-degrees
    `{0, 1, 4}`), not a privileged (e.g. triangular) subset. -/
theorem depth_spectrum_unrestricted (d : Nat) :
    polyDepth d (genExp d) ∧ ∀ j, j < d → ¬ E213.Lib.Math.Cauchy.DivergenceLadder.isConst
      (E213.Lib.Math.Cauchy.DepthTower.diffN j (genExp d)) :=
  genExp_depth_exact d

end E213.Lib.Math.Real213.SpiralLayer
