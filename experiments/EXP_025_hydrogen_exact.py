"""EXP_041: Hydrogen Energy Levels from Simplex (ch10)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "041", "Hydrogen Exact"
    def run(self):
        for n in [1, 2, 3, 4]:
            E = drlt.hydrogen_energy(n)
            obs = -13.606 / n**2
            self.log(f"E_{n} = {E:.4f} eV  (obs: {obs:.4f})")
            self.check(f"E_{n} exact", abs(E - obs) < 0.001)

        lyman_alpha = 1239.84 / (drlt.hydrogen_energy(2) - drlt.hydrogen_energy(1))
        self.log(f"Lyman-α = {lyman_alpha:.2f} nm  (obs: 121.57)")
        self.check("Lyman-α < 0.1%", abs(lyman_alpha - 121.57)/121.57 < 0.001)

if __name__ == "__main__": Exp().execute()
