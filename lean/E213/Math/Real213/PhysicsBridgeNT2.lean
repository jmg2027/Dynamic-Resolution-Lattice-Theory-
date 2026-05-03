import E213.Math.Real213.PhaseACMinimumProposition

/-!
# Research.Real213PhysicsBridgeNT2

**Cross-track bridge** for physics-track Phase 2 (atomic NT-sector = 2).

Physics-track Phase 2 (`E213/Physics/Phase2/`) has established:

  Atomicity (atom pair {2, 3}) → d = 5 → (3, 2) partition

The 2-block (NT = 2) is the smallest atomic block.  Unfolded as a
resolution sequence, its natural Lens output is **binary bisection** —
the dyadic geometry already formalized in `Real213DyadicBracket` +
`Real213DyadicTrajectory`.

This file is a **decoupled bridge**: 0 physics-track imports, only
analysis-track theorems re-stated under physics-friendly names.  When
physics-track Phase 2 reaches `Time.lean` / `Observable.lean`, this
file is `import`-ready as a single line.

## Bridge theorems

(B-1) `nt2_step_count`           — depth-n bisection: 2^n leaves.
(B-2) `nt2_left_trajectory`      — alwaysTrue: bracket (0, 1, n).
(B-3) `nt2_right_trajectory`     — alwaysFalse: bracket numB = 2^n.
(B-4) `nt2_atomic_yields_dyadic` — conjunctive bridge capstone.
-/

namespace E213.Math.Real213.PhysicsBridgeNT2

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.DyadicRiemann
  (riemannSampleSum riemannSampleSum_constCut riemannSampleSum_constCut_at)
open E213.Math.Real213.DyadicBracket
open E213.Math.Real213.ConsistentOracle
open E213.Math.Real213.DyadicTrajectory

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

/-- **B-4: NT=2 atomic block yields dyadic geometry** (bridge capstone).
    Function-eq form (Quot.sound-DIRTY at the riemannSampleSum funext
    boundary).  Prefer `nt2_atomic_yields_dyadic_at` for ∅-axiom. -/
theorem nt2_atomic_yields_dyadic (n a b : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).expE = n
    ∧ riemannSampleSum (constCutFn (constCut a b)) unitBracket n
        = constCut (2^n * a) b :=
  ⟨alwaysFalse_unit_numB n, alwaysTrue_unit_expE n,
   riemannSampleSum_constCut a b unitBracket n⟩

end E213.Math.Real213.PhysicsBridgeNT2
