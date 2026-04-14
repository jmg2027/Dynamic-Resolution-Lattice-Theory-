"""EXP_057: CKM Precision — Cabibbo + CP Phase (ch11)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "057", "CKM Precision"
    def run(self):
        # Cabibbo angle
        sc_bare = drlt.ckm_cabibbo(with_xi=False)
        sc_full = drlt.ckm_cabibbo(with_xi=True)
        obs_sc, unc_sc = 0.2253, 0.0008

        sig_bare = (sc_bare - obs_sc) / unc_sc
        sig_full = (sc_full - obs_sc) / unc_sc

        self.log(f"  sin theta_C (tree)  = {sc_bare:.6f}  ({sig_bare:+.2f}sigma)")
        self.log(f"  sin theta_C (+ Xi)  = {sc_full:.6f}  ({sig_full:+.2f}sigma)")
        self.log(f"  Observed            = {obs_sc} +/- {unc_sc}")

        # CP phase
        dcp = drlt.ckm_cp_phase()
        obs_dcp, unc_dcp = 68.8, 2.0
        sig_dcp = (dcp - obs_dcp) / unc_dcp
        self.log(f"\n  delta_CKM = pi/phi^2 = {dcp:.4f} deg  ({sig_dcp:+.3f}sigma)")
        self.log(f"  Observed  = {obs_dcp} +/- {unc_dcp} deg")

        # w parameter
        w = drlt.w_parameter()
        self.log(f"\n  w = n_S/(d*pi) = 3/(5pi) = {w:.6f}")

        self.check("sin theta_C Xi < 1sigma", abs(sig_full) < 1)
        self.check("Xi improves Cabibbo", abs(sig_full) < abs(sig_bare))
        self.check("delta_CKM < 0.1sigma", abs(sig_dcp) < 0.1)
        self.check("w = 3/(5pi)", abs(w - 3/(5*3.14159265)) < 1e-6)

if __name__ == "__main__": Exp().execute()
