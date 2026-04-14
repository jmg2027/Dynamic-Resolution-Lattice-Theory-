"""EXP_025: Baryon Asymmetry + Dark Energy (ch13)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "025", "Baryon Asymmetry & Cosmology"
    def run(self):
        eta = drlt.baryon_asymmetry()
        self.log(f"η_B = {eta:.2e}  (obs: 6.1e-10)")
        self.check("η_B ≈ 6.1e-10 (< 1%)", abs(eta - 6.1e-10)/6.1e-10 < 0.01)

        omega = drlt.dark_energy_fraction()
        self.log(f"Ω_Λ = {omega:.4f} = 1-1/π  (obs: 0.685)")
        self.check("Ω_Λ ≈ 0.682 (< 1%)", abs(omega - 0.685)/0.685 < 0.01)

        w = drlt.dark_energy_eos()
        self.log(f"w = {w:.1f}  (obs: ≈ -1)")
        self.check("w = -1", w == -1.0)

if __name__ == "__main__": Exp().execute()
