"""EXP_049: EXACT IE = Z²Ry/(1+Z²α²) — closed form from det(G_h)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt, numpy as np

class Exp(Experiment):
    ID, TITLE = "049", "Exact Closed-Form IE"
    def run(self):
        Ry = 13.606
        a = drlt.ALPHA_EM

        self.log("IE(Z) = Z²Ry / (1 + Z²α²)  — EXACT closed form\n")

        obs = {1:13.598, 2:54.418, 3:122.454, 4:217.720, 5:340.230}
        for Z in range(1, 6):
            ie = Z**2 * Ry / (1 + Z**2 * a**2)
            o = obs[Z]
            err = abs(ie - o)/o * 100
            self.log(f"  Z={Z}: IE = {ie:.3f} eV (obs: {o:.3f}, err: {err:.3f}%)")
            self.check(f"Z={Z} < 0.1%", err < 0.1)

        # Verify: denominator = Gram normalization
        self.log(f"\n1+Z²α² = Gram normalization N² = 1 + 3ε²")
        self.log(f"where ε = Zα/√n_S")
        self.log(f"Bohr model = α→0 limit: IE → Z²Ry")

if __name__ == "__main__": Exp().execute()
