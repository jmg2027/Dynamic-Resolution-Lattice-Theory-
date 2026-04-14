"""EXP_047: Lepton Mass Precision — Xi Improvement (ch09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "047", "Lepton Precision"
    def run(self):
        obs = 206.7682838
        r_bare = drlt.mu_e_ratio(with_xi=False)
        r_full = drlt.mu_e_ratio(with_xi=True)

        err_bare = (r_bare - obs) / obs
        err_full = (r_full - obs) / obs

        self.log(f"  m_mu/m_e (no Xi)  = {r_bare:.7f}  err = {err_bare*1e6:+.1f} ppm")
        self.log(f"  m_mu/m_e (with Xi)= {r_full:.10f}  err = {err_full*1e9:+.1f} ppb")
        self.log(f"  Observed          = {obs:.10f}")
        self.log(f"\n  Xi = {drlt.XI:.6e}")
        self.log(f"  Improvement: {abs(err_bare)/abs(err_full):.0f}x")

        self.check("Without Xi: ~0.02% level", abs(err_bare) < 3e-4)
        self.check("With Xi: sub-ppm", abs(err_full) < 1e-6)
        self.check("Xi improves precision", abs(err_full) < abs(err_bare))

if __name__ == "__main__": Exp().execute()
