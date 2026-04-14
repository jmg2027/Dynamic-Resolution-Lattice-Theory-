"""EXP_039: Molecular Bond Angles from Simplex Geometry (ch10)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "039", "Molecular Bond Angles"
    def run(self):
        for name, k, obs in [("CH₄", 0, 109.47), ("NH₃", 1, 107.80), ("H₂O", 2, 104.52)]:
            angle = drlt.bond_angle(k)
            err = abs(angle - obs)
            self.log(f"{name}: θ = {angle:.2f}°  (obs: {obs}°, Δ={err:.2f}°)")
            self.check(f"{name} < 1°", err < 1.0)

        e1 = drlt.hydrogen_energy(1)
        self.log(f"H ground state: E₁ = {e1:.3f} eV  (obs: -13.606)")
        self.check("E₁ = -13.606 eV", abs(e1 - (-13.606)) < 0.001)

if __name__ == "__main__": Exp().execute()
