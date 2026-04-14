"""EXP_047: Helium IE = 2Ry(1-4α_GUT) — connects to PMNS θ₁₃"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np

class Exp(Experiment):
    ID = "ATM_009", "Helium Analytic Solution"
    def run(self):
        Ry = 13.606  # eV
        a = drlt.ALPHA_GUT

        # IE(H) = Ry (verified in EXP_046)
        IE_H = Ry
        self.log(f"IE(H)  = Ry = {IE_H:.3f} eV")

        # IE(He) = 2Ry(1 - 4α_GUT)
        IE_He = 2 * Ry * (1 - 4*a)
        self.log(f"IE(He) = 2Ry(1-4α) = {IE_He:.3f} eV  (obs: 24.587)")
        self.check("IE(He) = 24.6 eV (0.1%)", abs(IE_He - 24.587)/24.587 < 0.001)

        # Connection to PMNS θ₁₃
        sin2_13 = a * (1 - 4*a)
        self.log(f"\nsin²θ₁₃ = α(1-4α) = {sin2_13:.6f}  (obs: 0.0220)")
        self.log(f"Same factor (1-4α) appears in both!")
        self.check("sin²θ₁₃ ≈ 0.022", abs(sin2_13 - 0.0220) < 0.001)

        # Screening coefficient
        sigma = 1/drlt.N_T + drlt.N_T * a
        self.log(f"\nσ = 1/n_T + n_T α = {sigma:.6f}")
        self.log(f"σ(obs) = 1 - IE/(4Ry) = {1 - 24.587/(4*Ry):.6f}")
        self.check("σ matches (0.1%)", abs(sigma - (1-24.587/(4*Ry))) < 0.001)

        # He⁺ (hydrogen-like Z=2)
        IE_He_plus = 4 * Ry
        self.log(f"\nIE(He⁺) = Z²Ry = {IE_He_plus:.3f} eV  (obs: 54.418)")
        self.check("IE(He⁺) = 4Ry", abs(IE_He_plus - 54.418)/54.418 < 0.001)

if __name__ == "__main__": Exp().execute()
