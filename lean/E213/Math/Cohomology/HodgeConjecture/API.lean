import E213.Math.Cohomology.HodgeConjecture.Foundation.Conjecture
import E213.Math.Cohomology.HodgeConjecture.Foundation.ConjectureLens
import E213.Math.Cohomology.HodgeConjecture.Foundation.Canonical
import E213.Math.Cohomology.HodgeConjecture.Foundation.Filled
import E213.Math.Cohomology.HodgeConjecture.Foundation.LensCata
import E213.Math.Cohomology.HodgeConjecture.Foundation.Complete
import E213.Math.Cohomology.HodgeConjecture.Toolkit.Primitives
import E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTrip
import E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTripMid
import E213.Math.Cohomology.HodgeConjecture.Toolkit.LensClassifier
import E213.Math.Cohomology.HodgeConjecture.Structure.Ring
import E213.Math.Cohomology.HodgeConjecture.Structure.Map
import E213.Math.Cohomology.HodgeConjecture.Refinement.LefschetzOneOne
import E213.Math.Cohomology.HodgeConjecture.Structure.PoincareDuality
import E213.Math.Cohomology.HodgeConjecture.Refinement.GeneralizedHodge
import E213.Math.Cohomology.HodgeConjecture.Refinement.StandardConjectures
import E213.Math.Cohomology.HodgeConjecture.Structure.HardLefschetz
import E213.OS.HodgeConjecture.Bridges.Tate
import E213.Math.Cohomology.HodgeConjecture.Pairing.HodgeIndex
import E213.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemann
import E213.Math.Cohomology.HodgeConjecture.Refinement.CupAtomicGeneration
import E213.Math.Cohomology.HodgeConjecture.Refinement.LefschetzHyperplane
import E213.OS.HodgeConjecture.Bridges.MumfordTate
import E213.OS.HodgeConjecture.Bridges.BlochBeilinson
import E213.Math.Cohomology.HodgeConjecture.Bridge.BeilinsonRegulator
import E213.Math.Cohomology.HodgeConjecture.Refinement.Voisin
import E213.OS.HodgeConjecture.Bridges.ChernCharacter
import E213.OS.HodgeConjecture.Bridges.HodgeTate
import E213.OS.HodgeConjecture.Bridges.BeilinsonLichtenbaum

/-!
# HodgeConjecture API — single import for the whole HC²¹³ + post-HC cluster

`import E213.Math.Cohomology.HodgeConjecture.API` exposes all 29
sub-modules of the HC²¹³ + post-HC²¹³ programme, organised into
six functional layers (architectural view):

  · **Foundation/**  (6) — the HC²¹³ claim itself + master capstone
  · **Toolkit/**     (4) — operational primitives (compute layer)
  · **Structure/**   (4) — multiplicative + duality structure
  · **Refinement/**  (6) — stronger / graded HC²¹³ statements
  · **Pairing/**     (2) — bilinear forms (Hodge Index, Hodge-Riemann)
  · **Bridge/**      (7) ★ — interfaces to other classical domains
                            (ℓ-adic, Galois, motivic, K-theory, p-adic,
                             L-functions, étale ↔ motivic)

The **Bridge/** layer is the public API surface — each file is a
classical-area entry point a non-213 mathematician can recognise
and start from.

See `INDEX.md` for navigation, `research-notes/hodge/ (G6-G11)` for the
philosophical / programme notes.
-/

namespace E213.Math.Cohomology.HodgeConjecture.API

/-- ★★★★★★★★★★ Master citation alias.

    The single citable theorem closing the Hodge conjecture in 213.
    Equivalent to
    `E213.Math.Cohomology.HodgeConjecture.Foundation.Complete.hodge_conjecture_213_complete`.

    Type: `HC_Universal ∧ HC_K32 ∧ HC_Involution`. -/
@[reducible] def HC213 :=
  @E213.Math.Cohomology.HodgeConjecture.Foundation.Complete.hodge_conjecture_213_complete

end E213.Math.Cohomology.HodgeConjecture.API
