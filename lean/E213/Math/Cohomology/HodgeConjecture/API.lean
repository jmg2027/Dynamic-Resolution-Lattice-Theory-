import E213.Math.Cohomology.HodgeConjecture.Core.Conjecture
import E213.Math.Cohomology.HodgeConjecture.Core.ConjectureLens
import E213.Math.Cohomology.HodgeConjecture.Core.Canonical
import E213.Math.Cohomology.HodgeConjecture.Core.Filled
import E213.Math.Cohomology.HodgeConjecture.Core.LensCata
import E213.Math.Cohomology.HodgeConjecture.Core.Complete
import E213.Math.Cohomology.HodgeConjecture.Toolkit.Primitives
import E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTrip
import E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTripMid
import E213.Math.Cohomology.HodgeConjecture.Toolkit.LensClassifier
import E213.Math.Cohomology.HodgeConjecture.Toolkit.Ring
import E213.Math.Cohomology.HodgeConjecture.Toolkit.Map
import E213.Math.Cohomology.HodgeConjecture.PostHC.LefschetzOneOne
import E213.Math.Cohomology.HodgeConjecture.PostHC.PoincareDuality
import E213.Math.Cohomology.HodgeConjecture.PostHC.GeneralizedHodge
import E213.Math.Cohomology.HodgeConjecture.PostHC.StandardConjectures
import E213.Math.Cohomology.HodgeConjecture.PostHC.HardLefschetz
import E213.Math.Cohomology.HodgeConjecture.PostHC.Tate
import E213.Math.Cohomology.HodgeConjecture.PostHC.HodgeIndex
import E213.Math.Cohomology.HodgeConjecture.PostHC.HodgeRiemann
import E213.Math.Cohomology.HodgeConjecture.PostHC.CupAtomicGeneration
import E213.Math.Cohomology.HodgeConjecture.PostHC.LefschetzHyperplane
import E213.Math.Cohomology.HodgeConjecture.PostHC.MumfordTate
import E213.Math.Cohomology.HodgeConjecture.PostHC.BlochBeilinson
import E213.Math.Cohomology.HodgeConjecture.PostHC.BeilinsonRegulator
import E213.Math.Cohomology.HodgeConjecture.PostHC.Voisin
import E213.Math.Cohomology.HodgeConjecture.PostHC.ChernCharacter
import E213.Math.Cohomology.HodgeConjecture.PostHC.HodgeTate
import E213.Math.Cohomology.HodgeConjecture.PostHC.BeilinsonLichtenbaum

/-!
# HodgeConjecture API — single import for the whole HC²¹³ + post-HC cluster

`import E213.Math.Cohomology.HodgeConjecture.API` exposes all 29 sub-
modules of the HC²¹³ + post-HC²¹³ programme:

  · `Core/`     — 6 files: HC²¹³ statement, K_{3,2} variant, canonical
                  capstone, filled extension, Lens-cata blueprint,
                  master capstone (★ `hodge_conjecture_213_complete`)
  · `Toolkit/`  — 6 files: support/fromList, round-trip, classifier,
                  Hodge ring, Hodge map
  · `PostHC/`   — 17 files: every classical Hodge-adjacent theorem
                  closed strict ∅-axiom this session series

See `INDEX.md` for navigation, `research-notes/G6-G11` for the
philosophical / programme notes.
-/

namespace E213.Math.Cohomology.HodgeConjecture.API

/-- ★★★★★★★★★★ Master citation alias.

    The single citable theorem closing the Hodge conjecture in 213.
    Equivalent to
    `E213.Math.Cohomology.HodgeConjecture.Core.Complete.hodge_conjecture_213_complete`.

    Type: `HC_Universal ∧ HC_K32 ∧ HC_Involution`. -/
@[reducible] def HC213 :=
  @E213.Math.Cohomology.HodgeConjecture.Core.Complete.hodge_conjecture_213_complete

end E213.Math.Cohomology.HodgeConjecture.API
