"""EXP_028: 200 Bytes = All of Physics from D=5 (ch01-ch13)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

class Exp(Experiment):
    ID, TITLE = "028", "200 Bytes = All Physics"
    def run(self):
        self.log(f"  D={drlt.D}, N_S={drlt.N_S}, N_T={drlt.N_T}, c={drlt.C_LATTICE}")
        self.log(f"  alpha_GUT = {drlt.ALPHA_GUT:.6f}")
        self.log(f"  Xi = {drlt.XI:.6e}")

        # Coupling constants
        self.log(f"\n  Coupling constants:")
        self.log(f"  1/alpha_s  = {drlt.inv_alpha_strong():.1f}  (obs 8.5)")
        self.log(f"  1/alpha_w  = {drlt.inv_alpha_weak():.1f}  (obs 29.6)")
        self.log(f"  1/alpha_em = {drlt.inv_alpha_em_bare():.2f}  (bare)")
        self.log(f"  1/alpha_em = {drlt.inv_alpha_em_corrected():.3f}  (corrected, obs 137.036)")
        self.log(f"  sin2_W     = {drlt.weinberg_angle():.4f}  (obs 0.2312)")
        self.check("1/alpha_em corrected ~ 137.036", abs(drlt.inv_alpha_em_corrected() - 137.036) < 0.1)

        # Masses
        self.log(f"\n  Masses:")
        self.log(f"  m_mu/m_e = {drlt.mu_e_ratio():.7f}  (obs 206.7682838)")
        self.log(f"  m_tau/m_mu = {drlt.tau_mu_ratio():.4f}  (obs 16.8170)")
        self.log(f"  m_p = {drlt.proton_mass():.3f} MeV  (obs 938.272)")
        self.log(f"  v_H = {drlt.electroweak_scale():.2f} GeV")
        self.check("m_mu/m_e sub-ppm", abs(drlt.mu_e_ratio() - 206.7682838)/206.7682838 < 1e-6)

        # Mixing
        self.log(f"\n  Mixing angles:")
        pmns = drlt.pmns_angles()
        for k, v in pmns.items(): self.log(f"  {k} = {v:.4f}")
        self.log(f"  sin_theta_C = {drlt.ckm_cabibbo():.4f}  (obs 0.2253)")
        self.log(f"  delta_CKM = {drlt.ckm_cp_phase():.2f} deg  (obs 68.8)")
        self.check("sin2_13 ~ 0.022", abs(pmns['sin2_13'] - 0.022) < 0.002)

        # Cosmology
        self.log(f"\n  Cosmology:")
        self.log(f"  eta_B = {drlt.baryon_asymmetry():.3e}  (obs 6.1e-10)")
        self.log(f"  Omega_L = {drlt.dark_energy_fraction():.4f}  (obs 0.685)")
        self.log(f"  N_gen = {drlt.generation_count()}  (obs 3)")
        self.check("eta_B ~ 6e-10", abs(drlt.baryon_asymmetry()/6.1e-10 - 1) < 0.01)
        self.check("Omega_L ~ 0.685", abs(drlt.dark_energy_fraction() - 0.685) < 0.001)

if __name__ == "__main__": Exp().execute()
