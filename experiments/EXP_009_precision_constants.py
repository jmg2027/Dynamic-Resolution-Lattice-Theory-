"""EXP_018: All Coupling Constants from d=5 (ch08)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "018", "Precision Coupling Constants"
    def run(self):
        self.log("=== Coupling Constants (ch08) ===")
        a3 = drlt.inv_alpha_strong()
        self.log(f"1/α₃ = {a3:.1f}  (obs: 8.47)")
        self.check("1/α₃ = 8.0", a3 == 8.0)

        a2 = drlt.inv_alpha_weak()
        self.log(f"1/α₂ = {a2:.1f}  (obs: 29.6)")
        self.check("1/α₂ = 30.0", a2 == 30.0)

        a1 = drlt.inv_alpha_em_bare()
        self.log(f"1/α₁ = {a1:.2f}  (= 6π²)")
        self.check("1/α₁ = 6π²", abs(a1 - 6*drlt.np.pi**2) < 1e-10)

        sw = drlt.weinberg_angle()
        self.log(f"sin²θ_W = {sw:.4f}  (obs: 0.2312)")
        self.check("sin²θ_W ≈ 0.23", abs(sw - 0.2312) < 0.003)

        bc = drlt.Simplex.random().binet_cauchy()
        self.log(f"Binet-Cauchy: {bc['SSS']}+{bc['SST']}+{bc['STT']}={bc['total']}")
        self.check("1+12+12 = 25 = d²", bc['check_d2'])

if __name__ == "__main__": Exp().execute()
