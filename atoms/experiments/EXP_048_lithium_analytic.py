"""EXP_048: Lithium IE = (Z-2σ)²Ry/4, σ=7/8"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt, numpy as np

class Exp(Experiment):
    ID, TITLE = "048", "Lithium Analytic Solution"
    def run(self):
        Ry = 13.606
        a = drlt.ALPHA_GUT
        d, n_S = drlt.D, drlt.N_S

        sigma_inner = 1 - n_S/(d**2 - 1)  # = 7/8
        self.log(f"σ_inner = 1 - n_S/(d²-1) = {sigma_inner:.4f} = 7/8")

        Z_eff = 3 - 2 * sigma_inner
        IE = Z_eff**2 * Ry / 4
        self.log(f"Z_eff = 3 - 2×7/8 = {Z_eff:.4f}")
        self.log(f"IE = {IE:.3f} eV  (obs: 5.392)")
        self.check("IE(Li) < 2%", abs(IE - 5.392)/5.392 < 0.02)

        self.log(f"\nn_S/(d²-1) = 3/24 = 1/8")
        self.log(f"Same denominator as Ξ: α_GUT/(d²-1)")
        self.check("σ = 7/8", abs(sigma_inner - 7/8) < 1e-10)

if __name__ == "__main__": Exp().execute()
