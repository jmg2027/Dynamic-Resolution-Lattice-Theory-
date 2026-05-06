import E213.Physics.Hadron.Bigrading
import E213.Physics.Hadron.Bridge
import E213.Physics.Hadron.Masses
import E213.Physics.Hadron.NeutronProton
import E213.Physics.Hadron.ProtonElectronRatio
import E213.Physics.Hadron.ProtonG
import E213.Physics.Hadron.ProtonMass
import E213.Physics.Hadron.QuarkHierarchy

/-! Spec-as-code entry point for `E213.Physics.Hadron`.

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
