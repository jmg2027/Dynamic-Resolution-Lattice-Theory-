"""EXP_052: Neutrino Mass Ratio — Democratic Seesaw 283->3.73 (ch11)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

class Exp(Experiment):
    ID, TITLE = "052", "Neutrino Ratio"
    def run(self):
        # Simple seesaw: m_nu ~ m_l^2/M_R => ratio = (m_tau/m_mu)^2 = 283
        r_simple = drlt.tau_mu_ratio()**2
        self.log(f"  Simple seesaw: m_nu3/m_nu2 = (m_tau/m_mu)^2 = {r_simple:.1f}")

        # DRLT democratic seesaw: D x T^-1 x D
        ratios = drlt.democratic_seesaw()
        r_drlt = ratios[0] / ratios[1]
        self.log(f"  DRLT seesaw eigenvalue ratios: {ratios}")
        self.log(f"  m_nu3/m_nu2 = {r_drlt:.2f}")

        r_obs = np.sqrt(2.453e-3 / 7.53e-5)  # sqrt(Dm32/Dm21) ~ 5.71
        self.log(f"  Observed: sqrt(Dm32/Dm21) = {r_obs:.2f}")
        self.log(f"\n  Improvement: {r_simple:.0f} -> {r_drlt:.2f} (obs {r_obs:.2f})")

        self.check(f"Ratio {r_drlt:.1f} << 283 (structural improvement)", r_drlt < r_simple / 5)
        self.check("Ratio order correct (1-50)", 0.5 < r_drlt < 50)
        self.check("Closer to observed than simple", abs(r_drlt - r_obs) < abs(r_simple - r_obs))

if __name__ == "__main__": Exp().execute()
