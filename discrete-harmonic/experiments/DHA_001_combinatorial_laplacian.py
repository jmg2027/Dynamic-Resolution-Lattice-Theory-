"""
DHA_001: Combinatorial Laplacian Spectrum of ∂(Δ⁴)
===================================================
Compute the full Hodge-Laplacian spectrum at each degree k
on the boundary of the 4-simplex (d=5 vertices).

Key questions:
1. Eigenvalues at each degree → DRLT constant connections?
2. Δ₂ on 10 faces = 10 channels → 1 SSS + 9 non-SSS structure?
3. Spectral ζ_Δ(s) vs DRLT ζ₉, ζ(2)?
4. S₅ representation decomposition of spectrum?

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import numpy as np
from itertools import combinations
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment


class CombLaplacian(Experiment):
    ID = "DHA_001"
    TITLE = "Combinatorial Laplacian Spectrum"

    def build_boundary_complex(self, d=5):
        """Build ∂(Δ⁴): all proper faces of the d-simplex.
        Excludes the top (d-1)-simplex itself → boundary ≅ S^{d-2}."""
        vertices = list(range(d))
        simplices = {}
        for k in range(d - 1):  # k = 0,...,d-2 (exclude top simplex)
            simplices[k] = sorted(combinations(vertices, k + 1))
        return simplices

    def build_boundary_operators(self, simplices, d=5):
        """Build boundary matrices ∂_k: C_k → C_{k-1}."""
        ops = {}
        for k in range(1, d - 1):  # k = 1,...,d-2
            n_src = len(simplices[k])
            n_tgt = len(simplices[k - 1])
            B = np.zeros((n_tgt, n_src))
            idx_map = {s: i for i, s in enumerate(simplices[k - 1])}
            for j, sigma in enumerate(simplices[k]):
                for fi in range(len(sigma)):
                    face = tuple(v for i, v in enumerate(sigma) if i != fi)
                    B[idx_map[face], j] = (-1) ** fi
            ops[k] = B
        return ops

    def hodge_laplacian(self, ops, simplices, k, d=5):
        """Δ_k = B_k^T B_k + B_{k+1} B_{k+1}^T on k-chains."""
        n_k = len(simplices[k])
        L = np.zeros((n_k, n_k))
        if k in ops:      # down part
            B = ops[k]
            L += B.T @ B
        if k + 1 in ops:  # up part
            B = ops[k + 1]
            L += B @ B.T
        return L

    def run(self):
        d = 5
        simplices = self.build_boundary_complex(d)
        ops = self.build_boundary_operators(simplices, d)

        self.log(f"\n  ∂(Δ⁴) — boundary of 4-simplex (d={d})")
        for k in simplices:
            self.log(f"    {k}-simplices: {len(simplices[k])}")

        # --- Test 1: Full Hodge Laplacian spectrum ---
        self.log("\n  === Test 1: Hodge Laplacian Spectrum ===\n")
        eigenvalues = {}
        eigenvectors = {}
        for k in range(d - 1):  # k = 0,...,d-2
            L = self.hodge_laplacian(ops, simplices, k, d)
            evals, evecs = np.linalg.eigh(L)
            eigenvalues[k] = evals
            eigenvectors[k] = evecs
            self._print_spectrum(k, evals)

        # Betti numbers
        betti = {}
        self.log("\n  Betti numbers:")
        for k in range(d - 1):
            betti[k] = int(np.sum(np.abs(eigenvalues[k]) < 1e-10))
            self.log(f"    β_{k} = {betti[k]}")
        self.check("β₀=1 (connected)", betti[0] == 1)
        self.check("β₁=0", betti[1] == 0)
        self.check("β₂=0", betti[2] == 0)
        self.check("β₃=1 (S³ top class)", betti[3] == 1)

        # --- Test 2-8: physics connections ---
        self._test_drlt_connections(eigenvalues, d)
        self._test_spectral_zeta(eigenvalues, d)
        self._test_channel_structure(eigenvalues, simplices, d)
        self._test_discrete_harmonics(eigenvalues, eigenvectors, simplices)
        self._test_euler(simplices, betti, d)

    def _print_spectrum(self, k, evals):
        """Pretty-print eigenvalues grouped by multiplicity."""
        self.log(f"  Δ_{k} eigenvalues ({len(evals)}×{len(evals)}):")
        groups = []
        for e in evals:
            if not groups or abs(e - groups[-1][0]) > 1e-10:
                groups.append([e, 1])
            else:
                groups[-1][1] += 1
        for val, mult in groups:
            self.log(f"    λ = {val:.6f}  (mult {mult})")

    def _test_drlt_connections(self, eigenvalues, d):
        """Test 2: eigenvalue connections to DRLT constants."""
        self.log("\n  === Test 2: Eigenvalue-DRLT Connections ===\n")
        # Δ₀: graph Laplacian of K₅ → eigenvalue d=5
        self.check("Δ₀ non-zero eigenvalue = d = 5",
                   abs(eigenvalues[0][1] - d) < 1e-10)
        self.check("Δ₀ non-zero mult = d-1 = 4",
                   int(np.sum(np.abs(eigenvalues[0] - d) < 1e-10)) == d - 1)

        # Non-zero eigenvalue sums and products
        for k in eigenvalues:
            nz = [e for e in eigenvalues[k] if abs(e) > 1e-10]
            if nz:
                self.log(f"  Δ_{k}: Σλ = {sum(nz):.4f}, "
                         f"Πλ = {np.prod(nz):.4f}, "
                         f"Σ1/λ = {sum(1/e for e in nz):.4f}")

    def _test_spectral_zeta(self, eigenvalues, d):
        """Test 3: spectral zeta ζ_Δ_k(s) vs DRLT ζ₉, ζ(2)."""
        self.log("\n  === Test 3: Spectral Zeta Function ===\n")
        zeta_9 = sum(1 / n**2 for n in range(1, 10))
        zeta_2 = np.pi**2 / 6

        for s in [1, 2, 3]:
            self.log(f"  s = {s}:")
            for k in eigenvalues:
                nz = [e for e in eigenvalues[k] if abs(e) > 1e-10]
                if nz:
                    z = sum(e**(-s) for e in nz)
                    self.log(f"    ζ_Δ_{k}({s}) = {z:.6f}")

        # Scan for ζ₉ match
        self.log(f"\n  Target: ζ₉ = {zeta_9:.6f},  ζ(2) = {zeta_2:.6f}")
        self.log(f"  Scanning ζ_Δ_k(s) for matches:")
        for k in eigenvalues:
            nz = [e for e in eigenvalues[k] if abs(e) > 1e-10]
            if not nz:
                continue
            for s_try in np.linspace(0.3, 5.0, 48):
                z = sum(e**(-s_try) for e in nz)
                if abs(z - zeta_9) / zeta_9 < 0.005:
                    self.log(f"    ζ_Δ_{k}({s_try:.3f}) = {z:.6f} ← ζ₉ match!")
                if abs(z - zeta_2) / zeta_2 < 0.005:
                    self.log(f"    ζ_Δ_{k}({s_try:.3f}) = {z:.6f} ← ζ(2) match!")

    def _test_channel_structure(self, eigenvalues, simplices, d):
        """Test 4: Δ₂ spectrum ↔ channel decomposition."""
        self.log("\n  === Test 4: Channel Structure (Δ₂ on faces) ===\n")
        evals2 = eigenvalues[2]
        nz2 = sorted([e for e in evals2 if abs(e) > 1e-10])
        self.log(f"  10 faces = C(5,3) = 10 channels")
        self.log(f"  Non-zero Δ₂ eigenvalues: {len(nz2)}")
        self.log(f"    values: {[f'{e:.4f}' for e in nz2]}")

        # Group eigenvalues — do they split into {1} + {9}?
        groups = []
        for e in nz2:
            if not groups or abs(e - groups[-1][0]) > 1e-10:
                groups.append([e, 1])
            else:
                groups[-1][1] += 1
        self.log(f"  Grouped: {[(f'{v:.4f}', m) for v, m in groups]}")

        # 10 faces decompose under S₅ into irreps
        # Standard result: C(5,3)=10 carries 1+9 or 4+6 etc.
        for v, m in groups:
            self.log(f"    λ={v:.4f}: mult {m}")

    def _test_discrete_harmonics(self, eigenvalues, eigenvectors, simplices):
        """Test 5: eigenvectors of Δ₂ as discrete harmonic basis."""
        self.log("\n  === Test 5: Discrete Harmonic Basis (Δ₂) ===\n")
        evals2 = eigenvalues[2]
        evecs2 = eigenvectors[2]
        labels = [str(s) for s in simplices[2]]

        # Show first few eigenvectors
        sorted_idx = np.argsort(evals2)
        for j in range(min(4, len(sorted_idx))):
            idx = sorted_idx[j]
            v = evecs2[:, idx]
            self.log(f"  Mode {j} (λ={evals2[idx]:.4f}):")
            for i, lbl in enumerate(labels):
                if abs(v[i]) > 0.05:
                    self.log(f"    {lbl}: {v[i]:+.4f}")
            self.log("")

    def _test_euler(self, simplices, betti, d):
        """Test 6: Euler characteristic verification."""
        self.log("\n  === Test 6: Euler Characteristic ===\n")
        chi = sum((-1)**k * len(simplices[k]) for k in range(d - 1))
        chi_b = sum((-1)**k * betti[k] for k in range(d - 1))
        self.log(f"  χ(∂Δ⁴) = 5 - 10 + 10 - 5 = {chi}")
        self.check("χ = 0 (S³ topology)", chi == 0)
        self.check("χ from Betti = 0", chi_b == 0)


if __name__ == "__main__":
    CombLaplacian().execute()
