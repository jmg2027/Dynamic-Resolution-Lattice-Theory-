"""EXP_058: Absolute Masses — mu/e, tau/mu, proton (ch09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "058", "Absolute Masses"
    def run(self):
        r_mu_e = drlt.mu_e_ratio()
        r_tau_mu = drlt.tau_mu_ratio()
        m_p = drlt.proton_mass()

        obs = [
            ("m_mu/m_e",  r_mu_e,            206.7682838, "ppb"),
            ("m_tau/m_mu", r_tau_mu,          16.8170,     "ppm"),
            ("m_tau/m_e",  r_mu_e * r_tau_mu, 3477.23,     "ppm"),
            ("m_p (MeV)",  m_p,              938.272,      "%"),
        ]

        self.log(f"  {'Observable':>14} {'DRLT':>14} {'Observed':>14} {'Error':>14}")
        self.log(f"  {'-'*60}")
        for name, pred, ob, unit in obs:
            err = (pred - ob) / ob
            if unit == "ppb":
                self.log(f"  {name:>14} {pred:>14.10f} {ob:>14.10f} {err*1e9:>+10.1f} ppb")
            elif unit == "ppm":
                self.log(f"  {name:>14} {pred:>14.6f} {ob:>14.6f} {err*1e6:>+10.1f} ppm")
            else:
                self.log(f"  {name:>14} {pred:>14.3f} {ob:>14.3f} {err*100:>+10.4f} %")

        self.check("m_mu/m_e sub-ppb", abs(r_mu_e - 206.7682838)/206.7682838 < 1e-9)
        self.check("m_tau/m_mu < 10 ppm", abs(r_tau_mu - 16.8170)/16.8170 < 10e-6)
        self.check("m_p exact", abs(m_p - 938.272)/938.272 < 1e-5)

if __name__ == "__main__": Exp().execute()
