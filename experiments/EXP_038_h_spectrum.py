"""
EXP_038: Hydrogen Spectrum from Local Hamiltonian
=================================================

Hydrogen = 1 simplex = {S₁,S₂,S₃,T₁,T₂}
"Empty" T₂ is NOT vacuum. It's the available slot for hopping.

H_{T₁} = Σ_j W_{T₁j} |ψ_j⟩⟨ψ_j|  (5×5 matrix)
Eigenvalues = energy levels. Just diagonalize. Done.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from experiment import Experiment
import numpy as np


class EXP_038(Experiment):
    ID = "038"
    TITLE = "H Spectrum"

    def run(self):
        self.log("=" * 60)
        self.log("HYDROGEN SPECTRUM FROM LOCAL HAMILTONIAN")
        self.log("=" * 60)

        # Quarks: pure spatial, orthogonal
        S1 = np.array([0,0,1,0,0], dtype=complex)
        S2 = np.array([0,0,0,1,0], dtype=complex)
        S3 = np.array([0,0,0,0,1], dtype=complex)

        # Electron: mostly T₁, small spatial leak
        leak = 0.15
        T1 = np.array([1, 0, leak, leak, leak], dtype=complex)
        T1 /= np.linalg.norm(T1)

        # T₂: NOT orthogonal to T₁! All vertices share the same C⁵.
        # In a real simplex, no vertex is perfectly orthogonal.
        # T₂ has its own C² direction but also has overlap with T₁.
        T2 = np.array([0.3, 0.9, 0.05, 0.05, 0.05], dtype=complex)
        T2 /= np.linalg.norm(T2)

        psi = [S1, S2, S3, T1, T2]
        labels = ["S₁","S₂","S₃","T₁","T₂"]

        # Compute W overlaps
        self.log("\n  Overlaps W_{T₁,j} = |⟨T₁|j⟩|²/5:")
        W = {}
        for j in range(5):
            if j == 3: continue
            w = abs(np.vdot(T1, psi[j]))**2 / 5
            W[j] = w
            role = "quark" if j < 3 else "hopping slot"
            self.log(f"    W(T₁,{labels[j]}) = {w:.6f}  ({role})")

        # Build H_{T₁}
        H = np.zeros((5,5), dtype=complex)
        for j, w in W.items():
            H += w * np.outer(psi[j], np.conj(psi[j]))

        eigs, vecs = np.linalg.eigh(H)
        idx = np.argsort(eigs)[::-1]
        eigs = eigs[idx]
        vecs = vecs[:, idx]

        self.log("\n  Eigenvalues of H_{T₁}:")
        for i, e in enumerate(eigs):
            v = vecs[:,i]
            t_w = abs(v[0])**2 + abs(v[1])**2
            s_w = 1 - t_w
            orb = "s" if t_w > 0.5 else "p"
            self.log(f"    λ_{i} = {e:.6f}  T:{t_w:.2f} S:{s_w:.2f} → {orb}-like")

        # Ratios
        self.log("\n  Ratios (vs λ₀):")
        for i in range(5):
            r = eigs[i]/eigs[0] if eigs[0]>1e-15 else 0
            h_pred = 1/(i+1)**2 if i < 4 else 0
            self.log(f"    λ_{i}/λ₀ = {r:.4f}  (1/n² = {h_pred:.4f})")

        # H vs H⁺: remove T₂
        self.log("\n  H vs H⁺ (remove hopping DOF):")
        H_ion = np.zeros((5,5), dtype=complex)
        for j, w in W.items():
            if j == 4: continue  # remove T₂
            H_ion += w * np.outer(psi[j], np.conj(psi[j]))
        eigs_ion = np.sort(np.linalg.eigvalsh(H_ion))[::-1]

        IE = eigs[0] - eigs_ion[0]
        self.log(f"    λ₀(H)  = {eigs[0]:.6f}")
        self.log(f"    λ₀(H⁺) = {eigs_ion[0]:.6f}")
        self.log(f"    IE = {IE:.6f}")
        self.log(f"    IE > 0 means H is more bound: {'✓' if IE>0 else '✗'}")
        self.check("IE > 0", IE > 0)
        self.check("3-fold degeneracy (p-like)", abs(eigs[1]-eigs[2])<1e-10 and abs(eigs[2]-eigs[3])<1e-10)


if __name__ == "__main__":
    EXP_038().execute()
