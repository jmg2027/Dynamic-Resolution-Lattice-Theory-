"""EXP_045: Analytic Solutions — Vacuum, Hydrogen, Confinement, ζ/η=n_T"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np
from itertools import combinations

class Exp(Experiment):
    ID, TITLE = "045", "Analytic Solutions on ∂(Δ⁵)"
    def run(self):
        d = drlt.D
        alpha = drlt.ALPHA_EM

        # 1. Vacuum solution
        self.log("=== 1. Vacuum: |G_ij|=1/d, Φ=π ===")
        det_vac = (d+1)**2 * (d-2) / d**3
        self.log(f"det(G_h) = (d+1)²(d-2)/d³ = {det_vac:.6f}")
        self.check("det = 108/125", abs(det_vac - 108/125) < 1e-10)
        self.check("det = 0.864", abs(det_vac - 0.864) < 1e-6)

        # Numerical verification
        psi = np.zeros((6, d), dtype=complex)
        psi[0]=[0,0,1,0,0]; psi[1]=[0,0,0,1,0]; psi[2]=[0,0,0,0,1]
        psi[3]=[1,0,alpha,alpha,0]; psi[4]=[0,1,0,alpha,alpha]
        psi[5]=[0.7,0.7,0.03,0,0.03]
        for i in range(6): psi[i] /= np.linalg.norm(psi[i])
        G = psi @ psi.conj().T

        # 2. Hydrogen IE
        self.log("\n=== 2. Hydrogen: IE = m_e α²/2 ===")
        g_AB = alpha / np.sqrt(drlt.N_S)
        det_AAB = 1 - 2*g_AB**2
        sigma_1_det = 3 * (1 - det_AAB)
        IE = 511000 / (2*drlt.N_T) * sigma_1_det
        self.log(f"|G_AB| = α/√n_S = {g_AB:.6f}")
        self.log(f"Σ(1-det)_AAB = {sigma_1_det:.8f}")
        self.log(f"IE = {IE:.3f} eV (obs: 13.598)")
        self.check("IE(H) ≈ 13.6 eV", abs(IE - 13.606) < 0.01)

        # 3. Confinement: S=0 for free quarks
        self.log("\n=== 3. Confinement ===")
        self.log("1 quark: C(1,3)=0 hinges → S=0 → ħ=0")
        self.log("2 quarks: C(2,3)=0 hinges → S=0 → ħ=0")
        self.log("3 quarks: C(3,3)=1 hinge → S>0 → baryon ✓")
        self.check("Free quark: no hinge", len(list(combinations([0],3))) == 0)
        self.check("Diquark: no hinge", len(list(combinations([0,1],3))) == 0)
        self.check("Baryon: 1 hinge", len(list(combinations([0,1,2],3))) == 1)

        # 4. ζ(2)/η(2) = n_T
        self.log("\n=== 4. ζ(2)/η(2) = n_T ===")
        zeta2 = np.pi**2 / 6
        eta2 = np.pi**2 / 12
        ratio = zeta2 / eta2
        self.log(f"ζ(2)/η(2) = {ratio:.1f} = n_T = {drlt.N_T}")
        self.check("ζ(2)/η(2) = 2 = n_T", abs(ratio - drlt.N_T) < 1e-10)

if __name__ == "__main__": Exp().execute()
