"""
DHA_005: Spectral Zeta Function on Simplicial Manifold
======================================================
Define ζ_M(s,ε) = Σ λ_k(ε)^{-s} where λ_k are eigenvalues of
the Gram-weighted Laplacian on the N-simplex manifold M(N,ε).

Key questions:
1. ζ_M(2,ε) at the Regge critical point → coupling constant?
2. How does the spectrum split 10 → 1+9 as ε grows?
3. Spectral zeta regularization → α_GUT?
4. Heat kernel K(t) = Σ e^{-λ_k t} and partition function

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import numpy as np
from itertools import combinations
from scipy.optimize import minimize_scalar
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment


class SpectralZeta(Experiment):
    ID = "DHA_005"
    TITLE = "Spectral Zeta Function"

    def build_face_laplacian(self, d, eps, spatial, temporal):
        """Gram-weighted Laplacian on faces of ∂(Δ⁴)."""
        faces = list(combinations(range(d), 3))
        n = len(faces)

        # Gram matrix G(ε)
        G = np.eye(d)
        w = np.zeros(d)
        for s in spatial:
            w[s] = 1.0
        e_t = np.zeros(d)
        e_t[temporal[0]] = 1.0
        G += eps * (np.outer(e_t, w) + np.outer(w, e_t))

        # Face weights = √det(G_face)
        weights = []
        for f in faces:
            idx = list(f)
            G_sub = G[np.ix_(idx, idx)]
            det = max(np.linalg.det(G_sub), 0)
            weights.append(np.sqrt(det))

        # Adjacency: faces sharing an edge, weighted by geometric mean
        A = np.zeros((n, n))
        for i, f1 in enumerate(faces):
            for j, f2 in enumerate(faces):
                if i >= j:
                    continue
                if len(set(f1) & set(f2)) == 2:
                    w_ij = np.sqrt(weights[i] * weights[j])
                    A[i, j] = A[j, i] = w_ij

        D = np.diag(A.sum(axis=1))
        L = D - A
        return L, faces, weights

    def classify_face(self, f, spatial, temporal):
        """Classify face as SSS, SST, or STT."""
        ns = sum(1 for v in f if v in spatial)
        if ns == 3:
            return 'SSS'
        elif ns == 2:
            return 'SST'
        else:
            return 'STT'

    def run(self):
        d = 5
        spatial = [0, 1, 2]
        temporal = [3, 4]

        # Test 1: Spectral zeta as function of ε
        self.log("\n  === Test 1: ζ_M(s,ε) vs ε ===\n")
        self._test_zeta_vs_eps(d, spatial, temporal)

        # Test 2: Eigenvalue splitting pattern
        self.log("\n  === Test 2: Eigenvalue Splitting ===\n")
        self._test_splitting(d, spatial, temporal)

        # Test 3: Spectral dimension
        self.log("\n  === Test 3: Spectral Dimension ===\n")
        self._test_spectral_dimension(d, spatial, temporal)

        # Test 4: Heat kernel
        self.log("\n  === Test 4: Heat Kernel ===\n")
        self._test_heat_kernel(d, spatial, temporal)

        # Test 5: Spectral zeta at critical point
        self.log("\n  === Test 5: ζ at Regge Critical Point ===\n")
        self._test_at_critical_point(d, spatial, temporal)

    def _test_zeta_vs_eps(self, d, spatial, temporal):
        """Compute ζ(s,ε) for s=1,2 across ε range."""
        self.log("  ε       | λ_min   | λ_max   | ζ(1)     | ζ(2)     | ζ(2)/d²")
        self.log("  " + "-" * 68)

        for eps in [0.0, 0.05, 0.10, 0.15, 0.157787, 0.20, 0.25, 0.30]:
            L, faces, weights = self.build_face_laplacian(d, eps, spatial, temporal)
            evals = np.sort(np.linalg.eigvalsh(L))
            nz = [e for e in evals if e > 1e-10]

            if len(nz) == 0:
                continue
            lmin = min(nz)
            lmax = max(nz)
            z1 = sum(1/e for e in nz)
            z2 = sum(1/e**2 for e in nz)

            self.log(f"  {eps:.6f} | {lmin:.5f} | {lmax:.5f} | {z1:.6f} | {z2:.6f} | {z2/d**2:.6f}")

    def _test_splitting(self, d, spatial, temporal):
        """Track eigenvalue splitting as ε increases."""
        eps_max = 0.157787
        L, faces, weights = self.build_face_laplacian(d, eps_max, spatial, temporal)
        evals = np.sort(np.linalg.eigvalsh(L))

        self.log(f"  Eigenvalues at ε = {eps_max}:")
        for i, e in enumerate(evals):
            self.log(f"    λ_{i} = {e:.6f}")

        # Classify: which eigenvalues correspond to which channel type?
        evecs = np.linalg.eigh(L)[1]
        self.log(f"\n  Eigenvector channel content:")
        for j in range(len(evals)):
            v = evecs[:, j]
            content = {'SSS': 0, 'SST': 0, 'STT': 0}
            for i, f in enumerate(faces):
                ch = self.classify_face(f, spatial, temporal)
                content[ch] += v[i]**2
            label = max(content, key=content.get)
            self.log(f"    λ_{j} = {evals[j]:.4f}: "
                     f"SSS={content['SSS']:.3f} SST={content['SST']:.3f} "
                     f"STT={content['STT']:.3f} → {label}")

        # Count non-zero eigenvalues
        n_nonzero = sum(1 for e in evals if e > 1e-10)
        self.check(f"9 non-zero eigenvalues (= non-SSS channels)",
                   n_nonzero == 9)

    def _test_spectral_dimension(self, d, spatial, temporal):
        """Spectral dimension d_s = -2 d(log K)/d(log t) at t→0."""
        eps = 0.157787
        L, faces, weights = self.build_face_laplacian(d, eps, spatial, temporal)
        evals = np.sort(np.linalg.eigvalsh(L))
        nz = [e for e in evals if e > 1e-10]

        # Heat kernel K(t) = Σ e^{-λ_k t}
        ts = np.logspace(-2, 2, 50)
        ds = []
        for i in range(len(ts) - 1):
            t1, t2 = ts[i], ts[i+1]
            K1 = sum(np.exp(-e * t1) for e in nz)
            K2 = sum(np.exp(-e * t2) for e in nz)
            if K1 > 0 and K2 > 0:
                d_spec = -2 * (np.log(K2) - np.log(K1)) / (np.log(t2) - np.log(t1))
                ds.append((np.sqrt(t1*t2), d_spec))

        self.log(f"  Spectral dimension at ε = {eps}:")
        self.log(f"  t        | d_s")
        self.log("  " + "-" * 25)
        for t, d_s in ds[::5]:
            self.log(f"  {t:8.4f}  | {d_s:.4f}")

        # At t→0: d_s → topological dimension
        # At t→∞: d_s → 0 (finite system)
        d_s_small = ds[0][1] if ds else 0
        self.log(f"\n  d_s(t→0) ≈ {d_s_small:.2f}")
        self.check("Spectral dimension d_s > 0 at small t", d_s_small > 0)

    def _test_heat_kernel(self, d, spatial, temporal):
        """Heat kernel trace and partition function."""
        eps = 0.157787
        L, faces, weights = self.build_face_laplacian(d, eps, spatial, temporal)
        evals = np.sort(np.linalg.eigvalsh(L))
        nz = [e for e in evals if e > 1e-10]

        # Z(β) = Σ e^{-β λ_k} = "partition function"
        self.log(f"  Partition function Z(β) at ε = {eps}:")
        self.log(f"  β      | Z(β)     | Z/9    | -dlogZ/dβ")
        self.log("  " + "-" * 48)

        for beta in [0.01, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0]:
            Z = sum(np.exp(-beta * e) for e in nz)
            # Energy = -d/dβ log Z = Σ λ e^{-βλ} / Z
            E = sum(e * np.exp(-beta * e) for e in nz) / Z if Z > 0 else 0
            self.log(f"  {beta:.3f}  | {Z:8.4f} | {Z/9:.4f} | {E:.4f}")

        # At β→0: Z → N_eff = 9, equipartition
        Z_0 = len(nz)
        self.log(f"\n  Z(β→0) = {Z_0} = number of modes")
        self.check("Z(β→0) = 9 (9 propagating channels)", Z_0 == 9)

    def _test_at_critical_point(self, d, spatial, temporal):
        """Spectral analysis at the Regge critical point ε_max."""
        eps = 0.157787
        L, faces, weights = self.build_face_laplacian(d, eps, spatial, temporal)
        evals = np.sort(np.linalg.eigvalsh(L))
        nz = sorted([e for e in evals if e > 1e-10])

        self.log(f"  At Regge critical point ε = {eps}:")
        self.log(f"  Non-zero eigenvalues: {[f'{e:.4f}' for e in nz]}")

        # Spectral zeta values
        for s in [1, 2, 3]:
            z = sum(e**(-s) for e in nz)
            self.log(f"  ζ_M({s}) = {z:.8f}")

        # Compare with DRLT constants
        zeta_9 = sum(1/n**2 for n in range(1, 10))
        zeta_2 = np.pi**2 / 6
        alpha_GUT = 6 / (25 * np.pi**2)

        z2 = sum(e**(-2) for e in nz)
        self.log(f"\n  Comparisons:")
        self.log(f"    ζ_M(2) = {z2:.8f}")
        self.log(f"    ζ₉     = {zeta_9:.8f}")
        self.log(f"    ζ(2)   = {zeta_2:.8f}")

        # Try: is 1/(d² × ζ_M(2)) a coupling constant?
        alpha_M = 1 / (d**2 * z2)
        self.log(f"    1/(d²ζ_M(2)) = {alpha_M:.8f}")
        self.log(f"    α_GUT        = {alpha_GUT:.8f}")
        self.log(f"    ratio         = {alpha_M/alpha_GUT:.4f}")

        # Rescaled spectral zeta
        # What if we normalize eigenvalues by d?
        nz_norm = [e/d for e in nz]
        z2_norm = sum(e**(-2) for e in nz_norm)
        alpha_norm = 1 / (d**2 * z2_norm)
        self.log(f"\n  With normalized eigenvalues (λ/d):")
        self.log(f"    ζ_M(2,norm) = {z2_norm:.8f}")
        self.log(f"    1/(d²ζ_M(2,norm)) = {alpha_norm:.8f}")
        self.log(f"    Ratio to α_GUT = {alpha_norm/alpha_GUT:.4f}")

        # Product of eigenvalues = det (regularized)
        log_det = sum(np.log(e) for e in nz)
        self.log(f"\n  log det'(Δ) = {log_det:.4f}")
        self.log(f"  det'(Δ) = {np.exp(log_det):.4f}")
        self.log(f"  det'(Δ)^{1/len(nz)} = {np.exp(log_det/len(nz)):.4f}")

        # Key insight: the geometric mean eigenvalue
        geom_mean = np.exp(log_det / len(nz))
        self.log(f"  Geometric mean eigenvalue = {geom_mean:.6f}")
        self.log(f"  Geometric mean / d = {geom_mean/d:.6f}")

        self.check("ζ_M(2) > 0 (positive spectral zeta)", z2 > 0)
        self.check("All eigenvalues > 0 (no zero modes except 1)",
                   len(nz) == 9)


if __name__ == "__main__":
    SpectralZeta().execute()
