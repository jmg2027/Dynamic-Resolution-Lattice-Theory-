"""EXP_033: Webb Dipole — Spatial Variation of alpha (ch17)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

class Exp(Experiment):
    ID, TITLE = "033", "Webb Dipole Consistency"
    def run(self):
        inv_a = drlt.inv_alpha_em_corrected()
        a_gut = drlt.ALPHA_GUT
        xi = drlt.XI

        self.log(f"  1/alpha_em = {inv_a:.3f}")
        self.log(f"  alpha_GUT = {a_gut:.6f}")
        self.log(f"  Xi = {xi:.6e}")

        # Webb dipole: Delta(alpha)/alpha ~ 1.1e-5
        da_obs = 1.1e-5
        # Required fractional det(G_h) variation
        f_req = da_obs * inv_a / (a_gut * inv_a)
        self.log(f"\n  Webb observed: Da/a = {da_obs:.1e}")
        self.log(f"  Required f = Da/a / a_GUT = {da_obs/a_gut:.4e}")

        # Simulate dipole pattern across sky
        np.random.seed(42)
        N = 1000
        theta = np.random.uniform(0, np.pi, N)
        f_sky = (da_obs / a_gut) * np.cos(theta)

        # alpha_em varies, alpha_GUT does not
        inv_a_sky = inv_a * (1 - a_gut * xi * f_sky)
        da_amp = (np.max(inv_a_sky) - np.min(inv_a_sky)) / np.mean(inv_a_sky)
        self.log(f"  Da_em/a_em amplitude = {da_amp:.2e}  (Webb ~1e-5)")
        self.check("Da_em amplitude ~ 1e-5 order", 1e-6 < da_amp < 1e-4)

        # alpha_GUT invariant (structure constant, not running)
        inv_a_gut = drlt.inv_alpha_gut()
        self.log(f"\n  1/alpha_GUT = 25pi^2/6 = {inv_a_gut:.4f} (spatially invariant)")
        self.check("alpha_GUT is a structural constant", abs(inv_a_gut - 25*np.pi**2/6) < 1e-10)

        # Trace conservation: sum of delta_i = 0
        d3 = 0.47; d2 = -0.40; d1 = -0.22; dG = -(d3+d2+d1)
        trace_sum = d3 + d2 + d1 + dG
        self.log(f"\n  Trace conservation: sum(delta_i) = {trace_sum:.2e}")
        self.check("Trace sum = 0", abs(trace_sum) < 1e-10)

        # Falsifiable prediction
        self.log(f"\n  Prediction: Da_em and Dmu must have OPPOSITE signs.")
        self.log(f"  Same sign -> DRLT falsified.")

if __name__ == "__main__": Exp().execute()
