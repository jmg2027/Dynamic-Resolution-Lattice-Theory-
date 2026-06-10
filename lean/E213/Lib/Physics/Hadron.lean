import E213.Lib.Physics.Hadron.Bigrading
import E213.Lib.Physics.Hadron.Bridge
import E213.Lib.Physics.Hadron.Masses
import E213.Lib.Physics.Hadron.NeutronProton
import E213.Lib.Physics.Hadron.ProtonElectronRatio
import E213.Lib.Physics.Hadron.ProtonG
import E213.Lib.Physics.Hadron.ProtonMass
import E213.Lib.Physics.Hadron.QuarkHierarchy
import E213.Lib.Physics.Hadron.MtOverMc

/-! Spec-as-code entry point for `E213.Lib.Physics.Hadron`.

  Hadron-mass cluster.

  ## Proton + neutron

    * `ProtonMass`         — m_p exact (target 938.27 MeV)
    * `ProtonG`            — proton g-factor
    * `ProtonElectronRatio` — m_p / m_e
    * `NeutronProton`      — n / p mass ratio
    * `Masses`             — full hadron-mass catalogue
                             (m_π / m_ω / m_J/ψ etc.)

  ## Quark structure

    * `QuarkHierarchy`     — quark-mass tower combinatorics
    * `Bigrading`          — bigraded representation underpinning
                             the hadron multiplet

  ## Bridge

    * `Bridge`             — Math.Cohomology / Physics.Foundations
                             cross-reference layer.
-/
