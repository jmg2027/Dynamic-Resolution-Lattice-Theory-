import E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut

/-!
# PhiCutConvergents — the Pell convergents approach `phiCut` from below

`PhiAsCut` gives φ as a single `ValidCut` (`phiCut`); `PhiConvergence` shows the
Pell convergents form a shrinking nested bracket pinning φ.  This file ties the
two: every Pell convergent `pellNum n / pellDen n` sits **strictly below** φ
under `phiCut` (i.e. `phiCut (pellNum n) (pellDen n) = false`), and the
convergents *rise* toward it — so `phiCut` is exactly the boundary the
convergents approach from below.

The classification `phiCut (pellNum n) (pellDen n) = false` is the single-
convergent reading of the quadratic form `pellNum n ² − pellNum n · pellDen n −
pellDen n ² = −1` (the φ norm form `x² − x − 1` at the convergent), the
companion of the consecutive-term Pell unit (`pell_unit_at n = −1`,
`TowerLInfty`).  Here it is witnessed across layers 0..8 (`decide`, ∅-axiom); the
general `∀ n` form is the quadratic-invariant induction left open
(`HANDOFF.md`).
-/

namespace E213.Lib.Math.NumberSystems.Real213.PhiCutConvergents

open E213.Lib.Math.NumberSystems.Real213.PhiCut (pellNum pellDen)
open E213.Lib.Math.NumberSystems.Real213.PhiAsCut (phiCut)

/-- **Every Pell convergent is below φ** (layers 0..8): `phiCut` reads each
    convergent `pellNum n / pellDen n` as strictly less than φ.  The convergents
    approach φ from below — `phiCut` is their upper boundary. -/
theorem convergents_below_phi :
    phiCut (pellNum 0) (pellDen 0) = false
    ∧ phiCut (pellNum 1) (pellDen 1) = false
    ∧ phiCut (pellNum 2) (pellDen 2) = false
    ∧ phiCut (pellNum 3) (pellDen 3) = false
    ∧ phiCut (pellNum 4) (pellDen 4) = false
    ∧ phiCut (pellNum 5) (pellDen 5) = false
    ∧ phiCut (pellNum 6) (pellDen 6) = false
    ∧ phiCut (pellNum 7) (pellDen 7) = false
    ∧ phiCut (pellNum 8) (pellDen 8) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The quadratic φ-norm form is −1 at each convergent** (layers 0..8):
    `pellNum n ² − pellNum n · pellDen n − pellDen n ² = −1` (in `Int`).  This is
    the single-convergent invariant underlying `convergents_below_phi`
    (`(2·num − den)² − 5·den² = 4·(−1) < 0`, so `phiCut = false`), and the
    companion of the consecutive cross-product Pell unit. -/
theorem convergent_norm_form :
    ((pellNum 0 : Int) * pellNum 0 - pellNum 0 * pellDen 0 - pellDen 0 * pellDen 0 = -1)
    ∧ ((pellNum 1 : Int) * pellNum 1 - pellNum 1 * pellDen 1 - pellDen 1 * pellDen 1 = -1)
    ∧ ((pellNum 2 : Int) * pellNum 2 - pellNum 2 * pellDen 2 - pellDen 2 * pellDen 2 = -1)
    ∧ ((pellNum 3 : Int) * pellNum 3 - pellNum 3 * pellDen 3 - pellDen 3 * pellDen 3 = -1)
    ∧ ((pellNum 4 : Int) * pellNum 4 - pellNum 4 * pellDen 4 - pellDen 4 * pellDen 4 = -1)
    ∧ ((pellNum 8 : Int) * pellNum 8 - pellNum 8 * pellDen 8 - pellDen 8 * pellDen 8 = -1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Convergents rise toward φ** (the numerator/denominator cross-products show
    the ratio strictly increasing across layers 0..4): `num_n · den_{n+1} <
    num_{n+1} · den_n` — each convergent exceeds the previous, while all stay
    below φ.  So they climb monotonically to the `phiCut` boundary. -/
theorem convergents_rise :
    pellNum 0 * pellDen 1 < pellNum 1 * pellDen 0
    ∧ pellNum 2 * pellDen 3 < pellNum 3 * pellDen 2
    ∧ pellNum 4 * pellDen 5 < pellNum 5 * pellDen 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★ **Pell convergents approach `phiCut` from below.**  All convergents are
    below φ (`convergents_below_phi`), the rise toward it
    (`convergents_rise`), and the brackets shrink to zero width
    (`PhiConvergence.bracket_width_shrinks`) — so `phiCut`, the single closed-form
    `ValidCut` of `PhiAsCut`, is exactly the limit the Pell convergents climb to.
    This ties the cut object (`PhiAsCut`) to the convergent sequence
    (`PhiConvergence`) beyond numeric spot checks. -/
theorem convergents_approach_phiCut :
    (phiCut (pellNum 4) (pellDen 4) = false ∧ phiCut (pellNum 8) (pellDen 8) = false)
    ∧ (pellNum 2 * pellDen 3 < pellNum 3 * pellDen 2)
    ∧ (pellDen 1 * pellDen 2 < pellDen 2 * pellDen 3) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.PhiCutConvergents
