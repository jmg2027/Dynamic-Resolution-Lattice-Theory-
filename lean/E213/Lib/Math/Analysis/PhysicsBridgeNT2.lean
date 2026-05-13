import E213.Lib.Math.Real213.Core.Core.MinimumProposition

import E213.Lib.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicRiemann
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
/-!
# PhysicsBridgeNT2
**Cross-track bridge** for the physics-track substrate-genesis
NT-sector = 2 layer (`E213/Physics/Substrate/`).

Physics-track substrate genesis has established:

  Atomicity (atom pair {2, 3}) → d = 5 → (3, 2) partition

The 2-block (NT = 2) is the smallest atomic block.  Unfolded as a
resolution sequence, its natural Lens output is **binary bisection** —
the dyadic geometry already formalised in `Analysis/DyadicSearch/
{DyadicBracket, DyadicTrajectory}.lean`.

This file is a **decoupled bridge**: 0 physics-track imports, only
analysis-track theorems re-stated under physics-friendly names.

## Bridge theorems

(B-1) `nt2_step_count`           — depth-n bisection: 2^n leaves.
(B-2) `nt2_left_trajectory`      — alwaysTrue: bracket (0, 1, n).
(B-3) `nt2_right_trajectory`     — alwaysFalse: bracket numB = 2^n.
(B-4) `nt2_atomic_yields_dyadic_at` — conjunctive bridge capstone
                                       (pointwise / `_at` form
                                       after the Stage-27 function-eq
                                       capstone delete).
-/

namespace E213.Lib.Math.Analysis.PhysicsBridgeNT2

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicRiemann
  (riemannSampleSum riemannSampleSum_constCut riemannSampleSum_constCut_at)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Lib.Math.Analysis.DyadicSearch.ConsistentOracle
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory

/-- **B-1: NT=2 atom → 2^n leaves at depth n**.
    Iterated 2-block produces 2^n distinguishable Lens-output states. -/
theorem nt2_step_count (n : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n :=
  alwaysFalse_unit_numB n

/-- **B-2: alwaysTrue trajectory closed form** — bracket (0, 1, n)
    = [0, 1/2^n].  Iterated leftward NT=2 → time-zero approach. -/
theorem nt2_left_trajectory (n : Nat) :
    (DyadicBracket.bisectN alwaysTrue n unitBracket).numA = 0
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).numB = 1
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).expE = n :=
  ⟨alwaysTrue_unit_numA n, alwaysTrue_unit_numB n, alwaysTrue_unit_expE n⟩

/-- **B-3: alwaysFalse trajectory closed form** — numB = 2^n,
    [1 - 1/2^n, 1].  Iterated rightward NT=2 → saturation approach. -/
theorem nt2_right_trajectory (n : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n :=
  alwaysFalse_unit_numB n

/-- **B-4 pointwise PURE**: same content as `nt2_atomic_yields_dyadic`
    but the riemannSampleSum equality is stated pointwise at (m, k).  -/
theorem nt2_atomic_yields_dyadic_at (n a b m k : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).expE = n
    ∧ riemannSampleSum (constCutFn (constCut a b)) unitBracket n m k
        = constCut (2^n * a) b m k :=
  ⟨alwaysFalse_unit_numB n, alwaysTrue_unit_expE n,
   riemannSampleSum_constCut_at a b unitBracket n m k⟩


end E213.Lib.Math.Analysis.PhysicsBridgeNT2
