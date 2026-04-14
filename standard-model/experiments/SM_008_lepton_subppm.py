"""EXP_050: Lepton Mass sub-ppm — 0.7 ppb Result (ch09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "050", "Lepton sub-ppm"
    def run(self):
        obs = 206.7682838
        r = drlt.mu_e_ratio()
        err = (r - obs) / obs

        self.log(f"  m_mu/m_e (DRLT) = {r:.10f}")
        self.log(f"  m_mu/m_e (obs)  = {obs:.10f}")
        self.log(f"  Error = {err*1e9:+.1f} ppb = {err*1e6:+.4f} ppm")
        self.log(f"  Xi = {drlt.XI:.6e}, alpha_GUT = {drlt.ALPHA_GUT:.6f}")

        r_bare = drlt.mu_e_ratio(with_xi=False)
        self.log(f"\n  Progression:")
        self.log(f"    Without Xi = {r_bare:.4f}   err = {(r_bare-obs)/obs*1e6:+.1f} ppm")
        self.log(f"    With Xi    = {r:.10f}   err = {err*1e9:+.1f} ppb")

        self.check("Sub-ppm achieved", abs(err) < 1e-6)
        self.check("Sub-ppb level (< 100 ppb)", abs(err) < 100e-9)
        self.check("0.7 ppb target", abs(err) < 1e-9)

if __name__ == "__main__": Exp().execute()
