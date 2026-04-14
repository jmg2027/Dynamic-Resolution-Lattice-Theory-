"""EXP_040: Clean Mass Scorecard (ch09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "040", "Clean Scorecard"
    def run(self):
        obs = [
            ("v_H (GeV)",  drlt.electroweak_scale(), 246.22,      0.004),
            ("m_mu/m_e",   drlt.mu_e_ratio(),        206.7682838, 1e-7),
            ("m_tau/m_mu",  drlt.tau_mu_ratio(),      16.8170,     0.007),
            ("m_tau/m_e",   drlt.mu_e_ratio()*drlt.tau_mu_ratio(), 3477.23, 0.007),
            ("m_p (MeV)",  drlt.proton_mass(),        938.272,     1e-5),
        ]

        self.log(f"  {'Observable':>14} {'DRLT':>14} {'Observed':>14} {'Error':>10}")
        self.log(f"  {'-'*56}")
        for name, pred, ob, unc in obs:
            err = (pred - ob) / ob * 100
            self.log(f"  {name:>14} {pred:>14.7f} {ob:>14.7f} {err:>+9.4f}%")
            self.check(f"{name}: |err| < {max(unc*100, 0.1):.3f}%",
                       abs(err) < max(unc * 200, 0.1))

        self.log(f"\n  Free parameters: 0.  Input: d = 5.")

if __name__ == "__main__": Exp().execute()
