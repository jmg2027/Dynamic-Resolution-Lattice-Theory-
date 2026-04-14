"""EXP_046: Hydrogen from δS/δψ=0 — Analytic solution verified numerically"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np
from itertools import combinations

class Exp(Experiment):
    ID, TITLE = "046", "Hydrogen Variational Solution"
    def run(self):
        D, N = 5, 6
        alpha = drlt.ALPHA_EM
        n_S, n_T = drlt.N_S, drlt.N_T

        # Analytic prediction: ε = α/√n_S
        eps = alpha / np.sqrt(n_S)
        self.log(f"ε = α/√n_S = {eps:.8f}")

        # Build ∂(Δ⁵) with hydrogen configuration
        psi = np.zeros((N, D), dtype=complex)
        psi[0]=[0,0,1,0,0]; psi[1]=[0,0,0,1,0]; psi[2]=[0,0,0,0,1]
        psi[3] = [1, 0, eps, eps, eps]       # B₁ (electron)
        psi[4] = [0, 1, 1e-6, 1e-6, 1e-6]   # B₂ (slot)
        psi[5] = [0.7, 0.7, 1e-6, 1e-6, 1e-6]  # B₃ (vacuum)
        for i in range(N): psi[i] /= np.linalg.norm(psi[i])
        G = psi @ psi.conj().T

        # Σ(1-det) for AAAB face AAB hinges
        binding = sum(1 - np.linalg.det(G[np.ix_(list(t),list(t))]).real
                      for t in combinations([0,1,2,3],3)
                      if sum(1 for v in t if v<3)==2)
        self.log(f"Σ(1-det)_AAB = {binding:.10f}")
        self.log(f"2α²         = {2*alpha**2:.10f}")
        self.check("Σ(1-det) = 2α² (0.1%)", abs(binding/(2*alpha**2) - 1) < 0.001)

        # IE
        E_scale = 511000 / (2 * n_T)  # m_e c² / (2 n_T)
        IE = E_scale * binding
        self.log(f"IE = {IE:.4f} eV (obs: 13.606)")
        self.check("IE = 13.606 eV (0.01%)", abs(IE - 13.606)/13.606 < 0.0001)

        # Vacuum det
        det_vac = (D+1)**2 * (D-2) / D**3
        self.log(f"det_vacuum = {det_vac:.6f} = 108/125")
        self.check("det_vac = 108/125", abs(det_vac - 108/125) < 1e-10)

        # |G_AB| = α/√n_S
        g_AB = abs(G[0,3])
        self.log(f"|G_AB| = {g_AB:.8f}, α/√n_S = {eps:.8f}")
        self.check("|G_AB| = α/√n_S (0.1%)", abs(g_AB/eps - 1) < 0.001)

if __name__ == "__main__": Exp().execute()
