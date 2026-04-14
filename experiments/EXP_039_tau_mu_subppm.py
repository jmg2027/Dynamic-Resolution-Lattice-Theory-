"""EXP_055: m_tau/m_mu Precision — Hop Series (ch09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "055", "tau/mu Precision"
    def run(self):
        R_OBS = 16.8170
        R_UNC = 0.0011  # 68 ppm

        r2 = drlt.tau_mu_ratio(order=2)
        r3 = drlt.tau_mu_ratio(order=3)
        err2 = (r2 - R_OBS) / R_OBS
        err3 = (r3 - R_OBS) / R_OBS

        self.log(f"  m_tau/m_mu (order=2) = {r2:.6f}  err = {err2*1e6:+.1f} ppm")
        self.log(f"  m_tau/m_mu (order=3) = {r3:.8f}  err = {err3*1e6:+.1f} ppm")
        self.log(f"  Observed             = {R_OBS:.6f}  unc = {R_UNC/R_OBS*1e6:.0f} ppm")
        self.log(f"\n  Improvement: {abs(err2)*1e6:.0f} -> {abs(err3)*1e6:.0f} ppm")
        self.log(f"  x = n_T * alpha_GUT = {drlt.N_T * drlt.ALPHA_GUT:.8f}")
        self.log(f"  c3 = n_S/(d+1) = {drlt.N_S/(drlt.D+1):.4f}")

        self.check("Order 3 better than order 2", abs(err3) < abs(err2))
        self.check("Order 3 within expt uncertainty", abs(err3) < R_UNC/R_OBS)
        self.check("Order 3 < 10 ppm", abs(err3) < 10e-6)

if __name__ == "__main__": Exp().execute()
