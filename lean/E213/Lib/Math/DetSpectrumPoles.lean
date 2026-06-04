import E213.Lib.Math.MaxEntropy
import E213.Lib.Math.Cauchy.ZeroInfinityHole

/-!
# The det-spectrum's two poles are the two folds' non-values; the unit is the center

The determinant `q` of an order-2 orbit is read on the Casoratian `cas` (the discrete Wronskian) as
its geometric ratio (`DetZeroCollapse.cas_step : cas s (n+1) = q · cas s n`).  Two earlier results put
a **non-value** at each end of that spectrum, one per founding fold:

  - **Bottom — the multiplicative-fold hole (`0` = `∞`).**  At `q = 0` the Casoratian collapses to the
    value `0` (`ZeroInfinityHole.cas_zero_collapses`), and `0` is the single point with no reciprocal
    (`zero_no_reciprocal`) — the place `x ↦ 1/x` returns no value.  The orbit's area is crushed into
    the hole.
  - **Top — the additive-fold ceiling (maximum entropy).**  At `q = −1` the Casoratian is a non-constant
    period-2 oscillation, so it has **no finite difference-depth**
    (`WronskianDepth.cas_neg_unit_no_finite_depth`) — i.e. `MaxEntropy (cas s)`: no finite holonomic
    handle generates it, the non-surjectivity ceiling read on the sequence.

Between the hole and the ceiling sits the **magnitude unit `q = +1`** — the *only* determinant whose
Casoratian avoids **both** poles at once: with nonzero seed it is **never `0`** (conserved, so it never
reaches the multiplicative hole) **and** it is `polyDepthZ 0` (finite difference-depth, so it never
reaches the additive ceiling).  Doubly finite, the live full-dimensional orbit.

So the two degeneracies that bracket the live region are not two unrelated pathologies: they are the
**two folds each failing to return a value** — the multiplicative fold's hole (`0`/`∞`) and the
additive fold's ceiling (maximum entropy / non-surjection) — exactly the two "non-values" the number
tower is built to *exclude*.  The unit `±1` is where a genuine distinguishing survives; its `+1` face
survives in both folds, its `−1` face is itself the additive ceiling (a multiplicative unit that is an
additive non-value — the founding sign carrying the richness).
-/

namespace E213.Lib.Math.DetSpectrumPoles

open E213.Lib.Math.Cauchy.DetZeroCollapse (cas cas_conserved_unit)
open E213.Lib.Math.Cauchy.WronskianDepth (cas_unit_depth0 cas_neg_unit_no_finite_depth)
open E213.Lib.Math.Cauchy.ZeroInfinityHole (cas_zero_collapses)
open E213.Lib.Math.MaxEntropy (MaxEntropy)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ)

/-- ★★★★ **Two poles, one center.**  For an order-2 orbit `s` with determinant coefficient `q`:

  * `q = 0` — the Casoratian collapses into the **multiplicative hole** (`cas s (n+1) = 0`);
  * `q = +1` — with nonzero seed the Casoratian avoids **both** poles: it is never `0` (away from the
    hole) and is `polyDepthZ 0` (away from the maximum-entropy ceiling) — the doubly-finite center;
  * `q = −1` — with nonzero seed the Casoratian is **maximum-entropy** (no finite handle), the additive
    ceiling.

The two degeneracies bracketing the live region are the two founding folds each failing to return a
value; the magnitude unit is where a genuine distinguishing survives. -/
theorem det_spectrum_poles_and_center (p : Int) (s : Nat → Int) :
    (-- bottom: q = 0 collapses into the 0/∞ hole
      (∀ n, s (n + 2) = p * s (n + 1) - 0 * s n) → ∀ n, cas s (n + 1) = 0)
    ∧ (-- center: q = +1 avoids both poles (never 0, and depth-0)
      (∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) → cas s 0 ≠ 0 →
        (∀ n, cas s n ≠ 0) ∧ polyDepthZ 0 (cas s))
    ∧ (-- top: q = -1 is the maximum-entropy ceiling
      (∀ n, s (n + 2) = p * s (n + 1) - (-1) * s n) → cas s 0 ≠ 0 → MaxEntropy (cas s)) :=
  ⟨fun hrec n => cas_zero_collapses p s hrec n,
   fun hrec h0 =>
     ⟨fun n => by rw [cas_conserved_unit p s hrec n]; exact h0, cas_unit_depth0 p s hrec⟩,
   fun hrec h0 => cas_neg_unit_no_finite_depth p s hrec h0⟩

end E213.Lib.Math.DetSpectrumPoles
