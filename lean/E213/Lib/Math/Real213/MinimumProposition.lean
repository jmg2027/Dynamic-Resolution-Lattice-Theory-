import E213.Lib.Math.Analysis.Differentiation.ResolutionDepth
import E213.Lib.Math.Analysis.DyadicSearch.DyadicRiemann
import E213.Lib.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory

import E213.Lib.Math.Real213.CutContinuity
import E213.Lib.Math.Real213.CutPoset
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.Differentiation.Smooth
/-!
# 213-line minimum proposition — three forced iff statements

Mirror of the physics-track minimum proposition
(`only_one_cosmos_dim : ∀ n, Atomic n ↔ n = 5`).

Analysis-track question: **what is the smallest proposition 213 can
make about its line?**  Answer: three forced iff-form statements
that pin the 213 line down with no remaining freedom — no parameter,
no exception, no smoothing.

  (1) The resolution law is forced to be linear-in-degree.
  (2) The dyadic accumulator is forced to give a specific cut.
  (3) The "0+" boundary is forced to be Boolean-distinct from 0.

(Renamed 2026-05-05 from `PhaseACMinimumProposition.lean`; bundle
theorem dropped — only the three iff statements remain, since the
bundle was a trivial conjunction of them.)
-/

namespace E213.Lib.Math.Real213.MinimumProposition

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Real213.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicRiemann (riemannSampleSum riemannSampleSum_constCut)
open E213.Lib.Math.Analysis.Differentiation.Smooth (IsSmooth cutPowFnIsSmooth)
open E213.Lib.Math.Analysis.Differentiation.ResolutionDepth (cutPowFnIsSmooth_modulus)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Lib.Math.Analysis.DyadicSearch.ConsistentOracle
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory

/-- **(1) Only one resolution law**.

    For any polynomial-chain depth `n` and output precision `k`,
    the linearityModulus is forced to equal `n * k` — no other
    value is achievable from the 213 dyadic geometry. -/
theorem only_one_resolution_law (n k m : Nat) :
    (cutPowFnIsSmooth n).linearityModulus k = m ↔ m = n * k :=
  ⟨fun h => h.symm.trans (cutPowFnIsSmooth_modulus n k),
   fun h => (cutPowFnIsSmooth_modulus n k).trans h.symm⟩

/-- **(2) Only one dyadic accumulator** (cutEq form).

    For any rational `a/b` and depth `n`, the binary-tree sum on a
    constant function is forced to land on `constCut (2^n * a) b`
    pointwise — no π, no e, no transcendental smoothing. -/
theorem only_one_dyadic_accumulator (a b n : Nat) (c : Nat → Nat → Bool) :
    E213.Lib.Math.Real213.CutPoset.cutEq
      (riemannSampleSum (constCutFn (constCut a b)) unitBracket n) c
      ↔ E213.Lib.Math.Real213.CutPoset.cutEq c (constCut (2^n * a) b) :=
  ⟨fun h m k => (h m k).symm.trans (riemannSampleSum_constCut a b unitBracket n m k),
   fun h m k => (riemannSampleSum_constCut a b unitBracket n m k).trans (h m k).symm⟩

/-- **(3) Only one 0+ witness**.

    The Cauchy limit of the alwaysTrueUnit oracle at `(0, 1)` is
    forced to be `false`, while the 0-exact cut is forced to be
    `true` — the two cuts are Boolean-distinct, no gluing possible. -/
theorem only_one_zero_plus_witness :
    ((ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1
       ≠ (constCut 0 1) 0 1) ↔ True := by
  refine ⟨fun _ => trivial, fun _ h => ?_⟩
  rw [alwaysTrueUnit_limit_distinct_from_zero.1,
      alwaysTrueUnit_limit_distinct_from_zero.2] at h
  exact Bool.noConfusion h

end E213.Lib.Math.Real213.MinimumProposition
