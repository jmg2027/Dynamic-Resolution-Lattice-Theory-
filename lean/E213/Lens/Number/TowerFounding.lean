import E213.Lens.Number.DifferenceLensFounding
import E213.Lens.Number.RatioLensFounding
import E213.Lens.Number.CauchyLensFounding

/-!
# TowerFounding — the number tower `ℕ → ℤ → ℚ → ℝ` is a chain of Lens bundlings

Capstone of the tower-founding files.  `seed/AXIOM/06_lens_readings.md` §6.7's doctrine — *the
number systems are successive bundlings of one residue under different Lens choices* — is now a
theorem chain, each rung a construction on the previous and all grounded in the residue (the slash):

  * **`ℕ`** — `+` is the slash counted: `(x/y).leaves = x.leaves + y.leaves` (the count-Lens
    `⟨1,1,+⟩`, `Theory.Raw.leaves_slash`);
  * **`ℤ`** — the difference-Lens is the count-Lens *bundled into a group*: it is a slash-
    homomorphism, its additivity inherited directly from the count-Lens
    (`DifferenceLensFounding.difference_lens_slash_additive`);
  * **`ℚ`** — the ratio rung's lowest-terms (coprimality) condition is the difference-Lens unit
    `det P = NS − NT` (`RatioLensFounding.convergent_lowest_terms_is_det`);
  * **`ℝ`** — the Cauchy rung: the ratio convergents narrow to a single cut (residue)
    (`CauchyLensFounding`, `PhiCauchyLimit.phiCauchy_limit_eq_phiCut`).

No rung is imported; each is what the residue produces under one more Lens application.  This is the
foundational counterpart to `book/` (which *applies* the tower): here the tower itself is *founded*,
rung by rung, as a single theorem.
-/

namespace E213.Lens.Number.TowerFounding

open E213.Theory (Raw)
open E213.Lens.Number.DifferenceLensFounding (diffView difference_lens_slash_additive)
open E213.Lens.Number.RatioLensFounding (convergent_lowest_terms_is_det)
open E213.Lib.Math.Algebra.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11)
open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit (phiConvergentSeq phiCauchy_limit_eq_phiCut)

/-- ★★★★ **The number tower `ℕ → ℤ → ℚ → ℝ` is a chain of Lens bundlings.**  Four rungs, each a
    construction on the previous, all grounded in the residue's slash:

    1. **`ℕ`** — `+` is the slash counted: `(x/y).leaves = x.leaves + y.leaves`;
    2. **`ℤ`** — the difference-Lens is a slash-homomorphism (the count-Lens bundled into a group):
       `diffView (x/x') (y/y') = diffView x y + diffView x' y'`;
    3. **`ℚ`** — the lowest-terms condition is the difference-Lens unit:
       `Q00·Q11 = Q01² + (NS − NT)`;
    4. **`ℝ`** — the ratio convergents narrow to a single cut: `phiConvergentSeq.limit = phiCut`.

    No rung is imported; the whole tower is the residue read through successive Lens choices —
    count, difference, ratio, Cauchy-completion. -/
theorem number_tower_is_lens_bundling :
    (∀ (x y : Raw) (h : x ≠ y), (Raw.slash x y h).leaves = x.leaves + y.leaves)
    ∧ (∀ (x x' y y' : Raw) (h : x ≠ x') (h' : y ≠ y'),
        diffView (Raw.slash x x' h) (Raw.slash y y' h') = diffView x y + diffView x' y')
    ∧ (∀ n, Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT))
    ∧ (∀ m k : Nat,
        phiConvergentSeq.limit m k = E213.Lib.Math.NumberSystems.Real213.PhiAsCut.phiCut m k) :=
  ⟨Raw.leaves_slash, difference_lens_slash_additive, convergent_lowest_terms_is_det,
   phiCauchy_limit_eq_phiCut⟩

end E213.Lens.Number.TowerFounding
