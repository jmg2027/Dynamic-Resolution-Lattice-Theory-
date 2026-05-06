import E213.Lib.Physics.Capstones.FinitistObservableChain
import E213.Lib.Physics.Capstones.MasterCatalog
import E213.Lib.Physics.Capstones.PhysicsTrackComplete
import E213.Lib.Physics.Capstones.PureAtomicObservables
import E213.Lib.Physics.Capstones.ValidationStandardOne

/-! Spec-as-code entry point for `E213.Lib.Physics.Capstones`.

  Top-level physics-track capstones integrating the per-cluster
  results from `Physics/{AlphaEM, Mass, Hadron, Cosmology, Higgs,
  Mixing, Nuclear, ...}`.  These were previously hosted under
  `OS/Physics/Capstones/` (Phase A2 of the M14 refactor moved
  them home to Physics/).

  ## Files

    * `MasterCatalog`           — every precision target
                                  (1/α_em, m_p, m_μ/m_e, m_H, Ω_Λ,
                                  magic numbers, ...) in one synthesis
    * `PureAtomicObservables`   — observables expressible as
                                  atomic integers (no fits)
    * `PhysicsTrackComplete`    — completeness statement: every
                                  Standard-Model parameter is
                                  predicted from atomic integers
    * `ValidationStandardOne`   — DRLT validation standard
                                  (first half: precision theorem
                                  matching observation at ppb)
    * `FinitistObservableChain` — finite-resolution closure of
                                  the observable chain
-/
