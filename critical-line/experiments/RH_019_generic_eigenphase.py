"""
RH_019: Generic Eigenphase Pattern
====================================

For generic ψ_i ∈ ℂ^d, H = Ψ†Ψ (d×d) has eigenvalues all ~N/d.
The "soft boundary" is nearly invisible in magnitudes.

The INFORMATION is in:
  1. Eigenvalue spacings (GUE? GOE?)
  2. Eigenvector phases
  3. The complex pattern of H's off-diagonal elements
  4. How the d×d structure encodes "which 5 are chiral"

No artificial τ-construction. Just generic ℂ^d.

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class GenericEigenphase(Experiment):
    ID = "RH_019"
    TITLE = "Generic eigenphase pattern"

    def run(self):
        self.test1_eigenvalue_pattern()
        self.test2_eigenvector_phases()
        self.test3_spacing_statistics()
        self.test4_complex_pattern_vs_d()

    def _make_H(self, N, d, seed=42):
        """d×d matrix H = Ψ†Ψ for N random unit vectors in ℂ^d."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        H = psi.conj().T @ psi  # d×d, Hermitian, rank ≤ min(N,d)
        return H

    # ── Test 1: Eigenvalue Pattern ───────────────────────

    def test1_eigenvalue_pattern(self):
        """Eigenvalues of H = Ψ†Ψ: all ~N/d, study deviations."""
        self.log("\n═══ Test 1: Eigenvalue Pattern of H = Ψ†Ψ ═══")

        N = 100
        d_values = [5, 7, 9, 10, 15, 20]

        for d in d_values:
            H = self._make_H(N, d, seed=42)
            eigs = np.sort(np.linalg.eigvalsh(H))[::-1]
            mean_eig = N / d

            # Normalized deviations from mean
            devs = (eigs - mean_eig) / np.sqrt(mean_eig)
            self.log(f"\n  d={d}, N={N}, N/d={mean_eig:.1f}:")
            self.log(f"    eigenvalues: "
                     f"{[f'{e:.1f}' for e in eigs[:min(d,8)]]}")
            self.log(f"    deviations/√(N/d): "
                     f"{[f'{v:.2f}' for v in devs[:min(d,8)]]}")

        self.check("Eigenvalue pattern mapped", True)

    # ── Test 2: Eigenvector Phases ───────────────────────

    def test2_eigenvector_phases(self):
        """Phase structure of eigenvectors of H."""
        self.log("\n═══ Test 2: Eigenvector Phases ═══")
        self.log("  Complex pattern of d eigenvectors of H")

        N = 100
        d = 10

        H = self._make_H(N, d, seed=42)
        eigs, vecs = np.linalg.eigh(H)
        # Sort by eigenvalue descending
        idx = np.argsort(eigs)[::-1]
        eigs = eigs[idx]
        vecs = vecs[:, idx]

        self.log(f"\n  d={d}, N={N}")
        self.log(f"  Eigenvector phase matrix (arg(v_ij)):")

        # Phase matrix: θ_{ij} = arg(v_i[j])
        phase_matrix = np.angle(vecs)
        self.log(f"    (rows = components, cols = eigenvectors)")
        for i in range(min(d, 6)):
            row = [f"{phase_matrix[i,j]:>+6.2f}" for j in range(min(d, 6))]
            self.log(f"    {' '.join(row)}")

        # Inter-eigenvector phase differences
        self.log(f"\n  Phase differences between adjacent eigenvectors:")
        for kk in range(min(d-1, 8)):
            dot = vecs[:, kk].conj() @ vecs[:, kk+1]
            self.log(f"    k={kk},{kk+1}: phase={np.angle(dot):>+6.3f}  "
                     f"|dot| = {abs(dot):.4f}")

        self.check("Eigenvector phases mapped", True)

    # ── Test 3: Spacing Statistics ───────────────────────

    def test3_spacing_statistics(self):
        """GUE or GOE for eigenvalue spacings of H?"""
        self.log("\n═══ Test 3: Spacing Statistics (β=?) ═══")
        self.log("  H = Ψ†Ψ with ℂ^d vectors → expect β=2 (GUE)")

        d_values = [5, 10, 20]
        N = 200
        n_trials = 500

        for d in d_values:
            all_ratios = []
            for t in range(n_trials):
                H = self._make_H(N, d, seed=t + d * 1000)
                eigs = np.sort(np.linalg.eigvalsh(H))
                spacings = np.diff(eigs)
                for k in range(len(spacings) - 1):
                    s1, s2 = spacings[k], spacings[k+1]
                    if max(s1, s2) > 1e-15:
                        all_ratios.append(
                            min(s1, s2) / max(s1, s2))

            mean_r = np.mean(all_ratios)
            # GUE: 0.603, GOE: 0.536, Poisson: 0.386
            dist_gue = abs(mean_r - 0.603)
            dist_goe = abs(mean_r - 0.536)
            beta = 2 if dist_gue < dist_goe else 1
            self.log(f"  d={d:>2}: ⟨r⟩ = {mean_r:.4f} → β = {beta} "
                     f"({'GUE' if beta == 2 else 'GOE'})")

        self.check("Spacing statistics classified", True)

    # ── Test 4: Complex Pattern vs d ─────────────────────

    def test4_complex_pattern_vs_d(self):
        """How the off-diagonal H_{ij} complex pattern changes with d."""
        self.log("\n═══ Test 4: Off-Diagonal Complex Pattern ═══")
        self.log("  H_{ij} = Σ_k conj(ψ_k^i) ψ_k^j for i≠j")
        self.log("  Each H_{ij} ∈ ℂ — study phase distribution")

        N = 100
        d_values = [5, 7, 10, 15, 20]
        n_trials = 100

        self.log(f"\n  {'d':>3} | {'⟨|H_ij|⟩':>10} | {'⟨|H_ij|²⟩':>10} | "
                 f"{'phase unif (KS p)':>17}")
        self.log(f"  {'-'*3}-+-{'-'*10}-+-{'-'*10}-+-{'-'*17}")

        for d in d_values:
            mags = []
            phases = []
            for t in range(n_trials):
                H = self._make_H(N, d, seed=t + d * 2000)
                iu = np.triu_indices(d, k=1)
                off_diag = H[iu]
                mags.extend(np.abs(off_diag))
                phases.extend(np.angle(off_diag))

            from scipy import stats
            ks_stat, p_val = stats.kstest(
                np.array(phases),
                'uniform', args=(-np.pi, 2*np.pi))

            self.log(f"  {d:>3} | {np.mean(mags):>10.3f} | "
                     f"{np.mean(np.array(mags)**2):>10.3f} | "
                     f"{p_val:>17.4f}")

        self.check("Complex pattern explored", True)


if __name__ == "__main__":
    GenericEigenphase().execute()
