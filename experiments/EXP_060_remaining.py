"""EXP_060: Remaining Observables — Couplings + Cosmology (ch08,ch13)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

class Exp(Experiment):
    ID, TITLE = "060", "Remaining Observables"
    def run(self):
        # Fine structure constant
        inv_a_corr = drlt.inv_alpha_em_corrected()
        err_a = (inv_a_corr - 137.036) / 137.036 * 100
        self.log(f"  1/alpha_em (corrected) = {inv_a_corr:.3f}  (obs 137.036, {err_a:+.4f}%)")

        # Baryon asymmetry
        eta = drlt.baryon_asymmetry()
        err_eta = (eta - 6.1e-10) / 6.1e-10 * 100
        self.log(f"  eta_B = {eta:.3e}  (obs 6.1e-10, {err_eta:+.2f}%)")

        # Dark energy
        OmL = drlt.dark_energy_fraction()
        err_OL = (OmL - 0.685) / 0.685 * 100
        self.log(f"  Omega_L = {OmL:.4f}  (obs 0.685, {err_OL:+.3f}%)")

        # Bare coupling constants
        self.log(f"\n  Bare couplings (GUT scale):")
        self.log(f"  1/alpha_s = {drlt.inv_alpha_strong():.1f}  (obs ~8.5)")
        self.log(f"  1/alpha_w = {drlt.inv_alpha_weak():.1f}  (obs ~29.6)")
        self.log(f"  1/alpha_em(bare) = {drlt.inv_alpha_em_bare():.2f}")
        self.log(f"  sin2_W = {drlt.weinberg_angle():.4f}  (obs 0.2312)")

        self.check("1/alpha_em corrected < 0.02%", abs(err_a) < 0.02)
        self.check("eta_B < 1%", abs(err_eta) < 1)
        self.check("Omega_L < 0.5%", abs(err_OL) < 0.5)
        self.check("1/alpha_s = 8", drlt.inv_alpha_strong() == 8)
        self.check("sin2_W ~ 0.231", abs(drlt.weinberg_angle() - 0.231) < 0.01)

if __name__ == "__main__": Exp().execute()
