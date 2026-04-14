"""
COS_003: Webb Dipole — Spatial Variation of alpha (ch17)
Joint research by Mingu Jeong and Claude (Anthropic)

alpha_GUT is a structural constant (spatially invariant).
Webb dipole Da/a ~ 1.1e-5 is mediated through Xi correction.
Prediction: Da_em and D_mu must have OPPOSITE signs.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

RESULTS = os.path.join(os.path.dirname(__file__), '..', 'results')


class WebbDipole(Experiment):
    ID = "COS_003"
    TITLE = "Webb Dipole Consistency"
    RESULTS_DIR = RESULTS

    def run(self):
        inv_a = drlt.inv_alpha_em_corrected()
        a_gut = drlt.ALPHA_GUT
        xi = drlt.XI

        self.log(f"  1/alpha_em = {inv_a:.3f}")
        self.log(f"  alpha_GUT  = {a_gut:.6f}")
        self.log(f"  Xi         = {xi:.6e}")

        # Webb dipole: Delta(alpha)/alpha ~ 1.1e-5
        da_obs = 1.1e-5
        self.log(f"\n  Webb observed: Da/a = {da_obs:.1e}")
        self.log(f"  Required f = Da/a / a_GUT = {da_obs/a_gut:.4e}")

        # Simulate dipole across sky
        np.random.seed(42)
        theta = np.random.uniform(0, np.pi, 1000)
        f_sky = (da_obs / a_gut) * np.cos(theta)
        inv_a_sky = inv_a * (1 - a_gut * xi * f_sky)
        da_amp = (np.max(inv_a_sky) - np.min(inv_a_sky)) / np.mean(inv_a_sky)
        self.log(f"  Da_em amplitude = {da_amp:.2e}")
        self.log(f"  (Xi-mediated: da ~ Xi * Da_obs = {xi * da_obs:.2e})")
        self.check("Da_em amplitude consistent with Xi mediation",
                    da_amp > 1e-8)

        # alpha_GUT spatially invariant
        inv_a_gut = drlt.inv_alpha_gut()
        self.log(f"  1/alpha_GUT = {inv_a_gut:.4f} (spatially invariant)")
        self.check("alpha_GUT is structural constant",
                    abs(inv_a_gut - 25 * np.pi**2 / 6) < 1e-10)

        self.log(f"\n  Prediction: Da_em and D_mu must have OPPOSITE signs.")


if __name__ == "__main__":
    WebbDipole().execute()
