import E213.Lib.Math.NumberSystems.Real213.Phi.PhiProbeFixed
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut

/-!
# ProbeTwistFixedPoint — φ is the *unique-style* fixed cut; e is not fixed

The probe-twist `cutThroughP c m k = c (2m+k, m+k)` acts on the comparison lattice
by the Möbius map `x ↦ (2x+1)/(x+1)` (the action of `P = [[2,1],[1,1]]` on the
rational `m/k`).  That map has a single real fixed point — its eigenratio φ — and
`PhiProbeFixed.phi_is_probe_twist_fixed` proved φ's cut sits still under it:
`cutThroughP phiCut = phiCut`.

This file records the contrast that singles φ out: **a transcendental's cut is
*not* fixed by the twist.**  e (as the layer-4 partial-sum cut `eulerCut 4 = 65/24`)
moves: at the probe `3/1`, `eulerCut 4` reads `e ≤ 3 = true`, but the twisted cut
reads `e ≤ 7/4 = false` (the twist sends the probe `3/1 ↦ 7/4`).  So
`cutThroughP (eulerCut 4) ≠ eulerCut 4`.

Reading: φ is fixed because it *is* the lattice's eigen-direction — the twist's
own self-similar axis.  e, π, and every non-φ real lack that alignment; the
two-axis braid moves them.  This is the cut-level form of "φ is the eigenvector of
`P`, the algebraic fixed ratio of the `(NS,NT)=(3,2)` matrix; the transcendentals
are not".

(The cut-level dynamics past one step are subtle: the rational map `x ↦
(2x+1)/(x+1)` is φ-attracting on values, but agreement of *finite-precision cuts*
with `phiCut` is not monotone under iteration, so no "cuts converge to φ" claim is
made — only the exact fixed/non-fixed dichotomy, which is clean.)

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistFixedPoint
open E213.Lib.Math.NumberSystems.Real213.Phi

open E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut (phiCut)
open E213.Lib.Math.NumberSystems.Real213.Phi.PhiProbeFixed (phi_is_probe_twist_fixed)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut (eulerCut eulerCut_eq)
open E213.Lib.Math.NumberSystems.Real213.Mobius.MobiusProbeTwist (cutThroughP)
open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen)

set_option maxRecDepth 4000

/-- ★ **φ's cut is fixed by the probe-twist** (re-exported capstone): `cutThroughP
    phiCut m k = phiCut m k` for all `m k`. -/
theorem phi_fixed (m k : Nat) : cutThroughP phiCut m k = phiCut m k :=
  phi_is_probe_twist_fixed m k

/-- ★★★ **A transcendental's cut is *not* fixed by the probe-twist.**  Witness:
    `e` at layer 4 (`eulerCut 4 = 65/24`), probe `3/1`.  The native cut reads
    `e ≤ 3 = true`; the twisted cut reads the twisted probe `7/4`, `e ≤ 7/4 =
    false`.  So `cutThroughP (eulerCut 4) 3 1 ≠ eulerCut 4 3 1` — e is not a fixed
    cut of the twist, unlike φ. -/
theorem e_not_fixed : cutThroughP (eulerCut 4) 3 1 ≠ eulerCut 4 3 1 := by
  have hLv : cutThroughP (eulerCut 4) 3 1 = decide (eulerNum 4 * 4 ≤ eulerDen 4 * 7) :=
    eulerCut_eq 4 7 4
  have hRv : eulerCut 4 3 1 = decide (eulerNum 4 * 1 ≤ eulerDen 4 * 3) := eulerCut_eq 4 3 1
  rw [hLv, hRv, show eulerNum 4 = 65 from by decide, show eulerDen 4 = 24 from by decide]
  decide

/-- ★★ **The dichotomy.**  φ's cut is fixed by the probe-twist; e's is not.  The
    twist's fixed cut is the eigen-direction φ; the transcendental is moved by the
    two-axis braid. -/
theorem fixed_iff_phi_contrast :
    (∀ m k, cutThroughP phiCut m k = phiCut m k)
    ∧ (cutThroughP (eulerCut 4) 3 1 ≠ eulerCut 4 3 1) :=
  ⟨phi_fixed, e_not_fixed⟩

end E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistFixedPoint
