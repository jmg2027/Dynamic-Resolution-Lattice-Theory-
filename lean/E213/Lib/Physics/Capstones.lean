import E213.Lib.Physics.Capstones.MasterCatalog
import E213.Lib.Physics.Capstones.NSNTPi5Block
import E213.Lib.Physics.Capstones.PhysicsTrackComplete
import E213.Lib.Physics.Capstones.PureAtomicObservables
import E213.Lib.Physics.Capstones.PhiUnification

/-! Spec-as-code entry point for `E213.Lib.Physics.Capstones`.

  Top-level physics-track capstones integrating the per-cluster
  results from `Physics/{AlphaEM, Mass, Hadron, Cosmology, Higgs,
  Mixing, Nuclear, ...}`.

  ## Files

    * `MasterCatalog`           — every precision target
                                  (1/α_em, m_p, m_μ/m_e, m_H, Ω_Λ,
                                  magic numbers, ...) in one synthesis
    * `PureAtomicObservables`   — observables expressible as
                                  atomic integers (no fits)
    * `PhysicsTrackComplete`    — completeness statement: every
                                  Standard-Model parameter is
                                  predicted from atomic integers
    * `NSNTPi5Block`            — cross-observable bridge:
                                  m_p/m_e and 1/α_em(IR) gap
                                  share NS·NT·π⁵ skeleton
-/
