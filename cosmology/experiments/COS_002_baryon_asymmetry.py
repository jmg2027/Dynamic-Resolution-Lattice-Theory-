"""
COS_002: Baryon Asymmetry & Dark Energy (ch13)
Joint research by Mingu Jeong and Claude (Anthropic)

Zero-parameter predictions:
  eta_B = alpha_GUT^3 * (n_T/n_S) / pi  = 6.13e-10  (obs 6.1e-10, 0.5%)
  Omega_Lambda = (1-1/pi)(1+alpha_GUT/d) = 0.6850    (obs 0.685, 0.001%)
  w = -1  (exact, from simplex rigidity)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt


class BaryonAsymmetry(Experiment):
    ID = "COS_002"
    TITLE = "Baryon Asymmetry & Cosmology"

    def run(self):
        eta = drlt.baryon_asymmetry()
        self.log(f"  eta_B = {eta:.2e}  (obs: 6.1e-10)")
        self.check("eta_B ~ 6.1e-10 (< 1%)",
                    abs(eta - 6.1e-10) / 6.1e-10 < 0.01)

        omega = drlt.dark_energy_fraction()
        err = abs(omega - 0.685) / 0.685
        self.log(f"  Omega_Lambda = {omega:.4f} = (1-1/pi)(1+a_GUT/d)")
        self.log(f"    bare:   1 - 1/pi = {1-1/3.14159265:.4f}")
        self.log(f"    corr:   x (1 + alpha_GUT/d) = {omega:.4f}")
        self.log(f"    obs:    0.685")
        self.log(f"    error:  {err*100:.4f}%")
        self.check("Omega_Lambda ~ 0.685 (< 0.01%)", err < 0.0001)

        w = drlt.dark_energy_eos()
        self.log(f"  w = {w:.1f}  (obs: ~ -1)")
        self.check("w = -1", w == -1.0)


if __name__ == "__main__":
    BaryonAsymmetry().execute()
