"""EXP_059: Neutron-Proton Mass Diff — Geometric Factor Diagnostic (ch09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

class Exp(Experiment):
    ID, TITLE = "059", "n-p Mass Diff Diagnostic"
    def run(self):
        D, N_S, N_T = drlt.D, drlt.N_S, drlt.N_T
        a = drlt.ALPHA_GUT
        xi = drlt.XI
        S2 = 15 / (2 * np.pi**2)

        # Geometric factor candidates
        geom_current = N_S * (D - 1 + S2) / D**2
        OBS_NP = 1.2934  # MeV
        dm_quarks = 4.67 - 2.16  # MeV, PDG m_d - m_u

        self.log(f"  alpha_GUT = {a:.6f}, Xi = {xi:.6e}")
        self.log(f"  m_d - m_u = {dm_quarks:.2f} MeV (PDG)")
        self.log(f"  Geometric factor (current) = {geom_current:.6f}")
        self.log(f"  Dm_np (current) = {dm_quarks*geom_current:.4f} MeV  (obs {OBS_NP})")

        err = (dm_quarks * geom_current - OBS_NP) / OBS_NP * 100
        self.log(f"  Error: {err:+.2f}%")

        # Required geometric factor from observation
        geom_exact = OBS_NP / dm_quarks
        self.log(f"\n  Required geom factor: {geom_exact:.6f}")
        self.log(f"  Ratio current/required: {geom_current/geom_exact:.4f}")

        # Test with Xi correction
        dm_xi = dm_quarks * geom_current * (1 - xi)
        err_xi = (dm_xi - OBS_NP) / OBS_NP * 100
        self.log(f"  With Xi: {dm_xi:.4f} MeV  ({err_xi:+.2f}%)")

        self.log(f"\n  Conclusion: +{err:.0f}% overcount in geometric factor.")
        self.log(f"  Xi correction is secondary ({abs(xi)*100:.2f}%).")
        self.check("Geometric factor overcount ~11%", 5 < err < 15)
        self.check("Xi correction < 1%", abs(dm_xi - dm_quarks*geom_current)/OBS_NP*100 < 1)

if __name__ == "__main__": Exp().execute()
