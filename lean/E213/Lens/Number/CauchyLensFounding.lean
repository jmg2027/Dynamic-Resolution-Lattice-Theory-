import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit

/-!
# CauchyLensFounding — `ℝ` is the Cauchy rung, closing the number tower

`seed/AXIOM/06_lens_readings.md` §6.7 founds `ℝ` as the top tower rung above the ratio-Lens (`ℚ`):
*Cauchy trajectories over the chain — sequences whose readings narrow to a single residue at the
limit — give `ℝ`.*  The distinctive 213 content is that a Cauchy trajectory of cut-readings
**narrows to a single cut (a single residue)**, and that the ratio (`ℚ`) convergents complete to
exactly such a closed-form cut.

This file makes that the closing theorem of the tower:

  * a `CauchyCutSeq` (a Cauchy trajectory of cut-readings) has a `limit` that is a *single* cut —
    `Nat → Nat → Bool`, one residue reading — and the trajectory **stabilizes to it** past the
    modulus (`CauchyComplete.CauchyCutSeq.limit_eq_at`: `limit m k = cs i m k` for all `i ≥ N m k`);
  * the ratio convergent sequence is such a trajectory, and its Cauchy limit **is** the closed-form
    golden cut — `phiConvergentSeq.limit = phiCut` (`PhiCauchyLimit.phiCauchy_limit_eq_phiCut`).

So `ℝ` is the Cauchy completion of the ratio (`ℚ`) readings, and its elements are single cuts
(single residues) — exactly §6.7's "Cauchy trajectories narrowing to a single residue."  The number
tower `ℕ → ℤ → ℚ → ℝ` now stands rung by rung as a chain of Lens bundlings: count, difference,
ratio, Cauchy-completion — each a construction on the previous, none imported, all grounded in the
residue (`DifferenceLensFounding`, `RatioLensFounding`, here).  (Completeness — that the limit of a
Cauchy sequence of *valid* cuts is itself a valid cut — is `Analysis/CauchyCompleteValid`.)
-/

namespace E213.Lens.Number.CauchyLensFounding

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit (phiConvergentSeq phiCauchy_limit_eq_phiCut)

/-- ★★★ **`ℝ` is the Cauchy rung — trajectories narrow to a single cut, and `ℚ` completes into it.**
    Two facts close the number tower at `ℝ`:

    1. **a Cauchy trajectory narrows to a single residue** — for any `CauchyCutSeq`, the `limit`
       (one cut, one residue reading) equals the trajectory's reading at *every* index past the
       modulus (`CauchyCutSeq.limit_eq_at`); the trajectory stabilizes to a single cut;
    2. **`ℝ` wraps `ℚ`** — the ratio convergent sequence (`phiConvergentSeq`) is such a trajectory,
       and its Cauchy limit *is* the closed-form golden cut `phiCut`
       (`phiCauchy_limit_eq_phiCut`).

    So `ℝ` is the Cauchy completion of the ratio readings, its elements single cuts (single
    residues) — the top rung of the tower `ℕ → ℤ → ℚ → ℝ`, each rung a Lens bundling of the residue,
    none imported. -/
theorem cauchy_lens_founds_on_ratio :
    (∀ (ccs : CauchyCutSeq) (m k i : Nat), i ≥ ccs.N m k → ccs.limit m k = ccs.cs i m k)
    ∧ (∀ m k : Nat,
        phiConvergentSeq.limit m k = E213.Lib.Math.NumberSystems.Real213.PhiAsCut.phiCut m k) :=
  ⟨CauchyCutSeq.limit_eq_at, phiCauchy_limit_eq_phiCut⟩

end E213.Lens.Number.CauchyLensFounding
