"""
RH Connection Core Library
============================

Tools for connecting DRLT Gram matrices to the Riemann Hypothesis.

Key objects:
  - GramEnsemble: generate ensembles of Gram matrices from ℂ⁵
  - SpectralZeta: Z_N(s) = Σ μ_k^{-s} for W-graph Laplacian
  - GUEAnalysis: level spacing, pair correlation, β extraction
  - SpectralGap: δ(N) scaling analysis

The derivation chain:
  ℂ unique → β=2 → GUE → d=5 → ζ(2) → s=2

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys
import os
import numpy as np
from scipy.special import zeta as sp_zeta

# Import from parent DRLT library
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from drlt import D, N_S, N_T, ALPHA_GUT, ZETA_2, GramMatrix


# ═══════════════════════════════════════════════════════════════
#  GRAM ENSEMBLE
# ═══════════════════════════════════════════════════════════════

class GramEnsemble:
    """
    Generate and analyze ensembles of Gram matrices from ℂ^d vs ℝ^d.

    Key test: ℂ^d → β=2 (GUE), ℝ^d → β=1 (GOE).
    This is the foundational claim connecting DRLT to RH.
    """

    def __init__(self, N: int, d: int = D, n_realizations: int = 1000,
                 seed: int = 42):
        self.N = N
        self.d = d
        self.n_real = n_realizations
        self.rng = np.random.RandomState(seed)

    def _make_gram_complex(self):
        """Single realization: N random unit vectors in ℂ^d → β=2."""
        psi = self.rng.randn(self.N, self.d) + 1j * self.rng.randn(self.N, self.d)
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        psi = psi / norms
        G = psi @ psi.conj().T
        return G, psi

    def _make_gram_real(self):
        """Single realization: N random unit vectors in ℝ^d → β=1."""
        psi = self.rng.randn(self.N, self.d)
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        psi = psi / norms
        G = psi @ psi.T
        return G, psi

    def gram_eigenvalues(self, field='complex'):
        """
        Collect non-zero eigenvalues of G across realizations.

        Args:
            field: 'complex' for ℂ^d (β=2) or 'real' for ℝ^d (β=1)
        """
        maker = self._make_gram_complex if field == 'complex' else self._make_gram_real
        all_eigs = []
        for _ in range(self.n_real):
            G, _ = maker()
            eigs = np.linalg.eigvalsh(G)
            nonzero = eigs[eigs > 1e-10]
            all_eigs.append(np.sort(nonzero)[::-1])
        return all_eigs

    def overlap_distribution(self, field='complex'):
        """
        Collect all pairwise overlaps |⟨ψ_i|ψ_j⟩|² for i<j.

        For ℂ^d: E[|⟨ψ|ψ'⟩|²] = 1/d
        For ℝ^d: E[⟨ψ|ψ'⟩²] = 1/d
        But the DISTRIBUTIONS differ (β=2 vs β=1).
        """
        maker = self._make_gram_complex if field == 'complex' else self._make_gram_real
        all_overlaps = []
        for _ in range(self.n_real):
            G, _ = maker()
            N = G.shape[0]
            for i in range(N):
                for j in range(i+1, N):
                    all_overlaps.append(np.abs(G[i, j])**2)
        return np.array(all_overlaps)

    def max_overlap(self, field='complex'):
        """max_{i≠j} |⟨ψ_i|ψ_j⟩|² per realization — packing density measure."""
        maker = self._make_gram_complex if field == 'complex' else self._make_gram_real
        max_overlaps = []
        for _ in range(self.n_real):
            G, _ = maker()
            np.fill_diagonal(G, 0.0)
            max_overlaps.append(np.max(np.abs(G)**2))
        return np.array(max_overlaps)


# ═══════════════════════════════════════════════════════════════
#  GUE ANALYSIS
# ═══════════════════════════════════════════════════════════════

class GUEAnalysis:
    """
    Tools for testing GUE (β=2) statistics.

    Key signatures:
    - Level repulsion: P(s) ∝ s^β at small s (β=2 for GUE)
    - Wigner surmise: P₂(s) = (32/π²)s² exp(-4s²/π)
    - Pair correlation: R₂(r) = 1 - (sin πr / πr)²
    """

    @staticmethod
    def wigner_surmise_gue(s):
        """GUE Wigner surmise P₂(s) = (32/π²)s² exp(-4s²/π)."""
        return (32.0 / np.pi**2) * s**2 * np.exp(-4.0 * s**2 / np.pi)

    @staticmethod
    def wigner_surmise_goe(s):
        """GOE Wigner surmise P₁(s) = (π/2)s exp(-πs²/4)."""
        return (np.pi / 2.0) * s * np.exp(-np.pi * s**2 / 4.0)

    @staticmethod
    def spacings_from_ensemble(eig_list):
        """
        Compute normalized spacings from an ensemble of eigenvalue sets.

        Each entry in eig_list is a sorted array of d eigenvalues from
        one Gram matrix realization. We collect all (d-1) spacings from
        each, then normalize by the ensemble mean spacing.
        """
        all_spacings = []
        for eigs in eig_list:
            eigs = np.sort(eigs)
            diffs = np.diff(eigs)
            all_spacings.extend(diffs)
        all_spacings = np.array(all_spacings)
        mean_s = np.mean(all_spacings)
        if mean_s > 0:
            all_spacings = all_spacings / mean_s
        return all_spacings

    @staticmethod
    def fit_beta(spacings, s_max=1.0):
        """
        Extract level repulsion exponent β from P(s) ∝ s^β at small s.

        Uses log-log fit of the spacing distribution.
        Returns β and fit quality R².
        """
        spacings = spacings[spacings > 0]
        bins = np.linspace(0, s_max, 40)
        hist, edges = np.histogram(spacings, bins=bins, density=True)
        centers = 0.5 * (edges[:-1] + edges[1:])

        # Use bins where s > 0.05 and P(s) > 0 for log-log fit
        mask = (hist > 0) & (centers > 0.05) & (centers < s_max * 0.8)
        if np.sum(mask) < 4:
            return np.nan, 0.0

        log_s = np.log(centers[mask])
        log_p = np.log(hist[mask])

        coeffs = np.polyfit(log_s, log_p, 1)
        beta = coeffs[0]

        predicted = np.polyval(coeffs, log_s)
        ss_res = np.sum((log_p - predicted)**2)
        ss_tot = np.sum((log_p - np.mean(log_p))**2)
        r_squared = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0

        return beta, r_squared

    @staticmethod
    def ratio_statistic(eig_list):
        """
        Compute the ratio statistic r = min(s_n, s_{n-1}) / max(s_n, s_{n-1}).

        This does NOT require unfolding — it depends only on β:
          Poisson (β=0): ⟨r⟩ ≈ 0.386
          GOE (β=1):     ⟨r⟩ ≈ 0.536
          GUE (β=2):     ⟨r⟩ ≈ 0.603

        Reference: Atas et al., PRL 110, 084101 (2013).
        """
        all_ratios = []
        for eigs in eig_list:
            eigs = np.sort(eigs)
            spacings = np.diff(eigs)
            for k in range(len(spacings) - 1):
                s1, s2 = spacings[k], spacings[k+1]
                if max(s1, s2) > 1e-15:
                    all_ratios.append(min(s1, s2) / max(s1, s2))
        return np.array(all_ratios)

    # Theoretical ⟨r⟩ values from Atas et al. (2013)
    R_MEAN_POISSON = 0.3863   # β=0 (uncorrelated)
    R_MEAN_GOE = 0.5359       # β=1 (real symmetric)
    R_MEAN_GUE = 0.6027       # β=2 (complex Hermitian)

    @staticmethod
    def classify_beta(mean_r):
        """Classify β from mean ratio statistic ⟨r⟩."""
        d0 = abs(mean_r - GUEAnalysis.R_MEAN_POISSON)
        d1 = abs(mean_r - GUEAnalysis.R_MEAN_GOE)
        d2 = abs(mean_r - GUEAnalysis.R_MEAN_GUE)
        if d2 <= d1 and d2 <= d0:
            return 2, d2
        elif d1 <= d0:
            return 1, d1
        else:
            return 0, d0

    @staticmethod
    def gue_pair_correlation(r):
        """Theoretical GUE pair correlation: 1 - (sin πr / πr)²."""
        with np.errstate(divide='ignore', invalid='ignore'):
            sinc = np.where(np.abs(r) < 1e-15, 1.0, np.sin(np.pi * r) / (np.pi * r))
        return 1.0 - sinc**2


# ═══════════════════════════════════════════════════════════════
#  SPECTRAL ZETA FUNCTION Z_N(s)
# ═══════════════════════════════════════════════════════════════

class SpectralZeta:
    """
    Z_N(s) = Σ_{k=1}^{N-1} μ_k^{-s}

    where μ_k are non-zero eigenvalues of the W-graph Laplacian.

    Properties:
    - Converges for Re(s) > d_s/2 (d_s = spectral dimension)
    - Analytic continuation via eta-regularization
    - GUE zero statistics (from ℂ → β=2)
    """

    def __init__(self, laplacian_eigenvalues):
        """
        Args:
            laplacian_eigenvalues: non-zero eigenvalues of L (ascending)
        """
        eigs = np.sort(np.array(laplacian_eigenvalues))
        self.eigenvalues = eigs[eigs > 1e-12]  # remove zero mode

    def __call__(self, s):
        """Evaluate Z_N(s) = Σ μ_k^{-s}."""
        return np.sum(self.eigenvalues ** (-s))

    def evaluate_line(self, sigma, t_values):
        """Evaluate Z_N(σ + it) along a vertical line."""
        return np.array([self(complex(sigma, t)) for t in t_values])

    def find_zeros_on_line(self, sigma, t_range=(0.1, 50), n_points=2000):
        """
        Find approximate zeros of Z_N(σ + it) by sign changes of Re(Z).

        Returns t values where |Z_N(σ + it)| is minimized.
        """
        t_vals = np.linspace(t_range[0], t_range[1], n_points)
        z_vals = self.evaluate_line(sigma, t_vals)
        magnitudes = np.abs(z_vals)

        # Find local minima
        zeros = []
        for i in range(1, len(magnitudes) - 1):
            if magnitudes[i] < magnitudes[i-1] and magnitudes[i] < magnitudes[i+1]:
                if magnitudes[i] < 0.5 * np.mean(magnitudes):
                    zeros.append(t_vals[i])
        return np.array(zeros)

    def spectral_dimension(self, sigma_range=(0.5, 5.0), n_points=100):
        """
        Estimate spectral dimension d_s from Z_N(s) behavior.

        Z_N(s) diverges at s = d_s/2, so we look for the pole.
        """
        sigmas = np.linspace(sigma_range[0], sigma_range[1], n_points)
        z_real = np.array([np.real(self(s)) for s in sigmas])
        # d_s ≈ 2 × (location of maximum |Z_N|)
        idx_max = np.argmax(np.abs(z_real))
        return 2.0 * sigmas[idx_max]


# ═══════════════════════════════════════════════════════════════
#  SPECTRAL GAP ANALYSIS
# ═══════════════════════════════════════════════════════════════

class SpectralGap:
    """
    Analyze the resolution limit δ(N) of the Gram matrix ensemble.

    Self-contradiction boundary theorem:
    For N unit vectors in ℂ^d (d=5), define:
      δ(N) = 1 - max_{i≠j} |⟨ψ_i|ψ_j⟩|²
    This is the "minimum distinguishability" — how close the closest
    pair can be. For finite N, δ(N) > 0 always.

    As N → ∞, packing forces δ → 0, but Tr(G) = N < ∞ (axiom)
    bounds N, so the exact limit is unreachable.
    """

    @staticmethod
    def compute_resolution(N, d=D, n_trials=200, seed=42):
        """
        Compute δ(N) = 1 - max_{i≠j} |⟨ψ_i|ψ_j⟩|² for Gram matrices in ℂ^d.

        This measures the closest packing in CP^{d-1}.
        δ(N) > 0 always (self-contradiction boundary).
        δ(N) decreases as N grows (more vectors → closer packing).
        """
        rng = np.random.RandomState(seed)
        deltas = []
        for _ in range(n_trials):
            psi = rng.randn(N, d) + 1j * rng.randn(N, d)
            norms = np.linalg.norm(psi, axis=1, keepdims=True)
            psi = psi / norms
            G = psi @ psi.conj().T
            overlaps = np.abs(G)**2
            np.fill_diagonal(overlaps, 0.0)
            max_overlap = np.max(overlaps)
            deltas.append(1.0 - max_overlap)
        return np.array(deltas)

    @staticmethod
    def compute_min_eigenvalue_spacing(N, d=D, n_trials=200, seed=42):
        """
        Minimum eigenvalue spacing of the d×d compressed Gram matrix.

        For d non-zero eigenvalues: min_{k} |λ_{k+1} - λ_k|.
        This directly reflects β=2 level repulsion.
        """
        rng = np.random.RandomState(seed)
        min_spacings = []
        for _ in range(n_trials):
            psi = rng.randn(N, d) + 1j * rng.randn(N, d)
            norms = np.linalg.norm(psi, axis=1, keepdims=True)
            psi = psi / norms
            # Compressed d×d matrix H = Ψ†Ψ (same non-zero spectrum as G)
            H = psi.conj().T @ psi
            eigs = np.sort(np.linalg.eigvalsh(H))
            spacings = np.diff(eigs)
            min_spacings.append(np.min(spacings))
        return np.array(min_spacings)

    @staticmethod
    def fit_scaling(N_values, delta_means):
        """
        Fit δ(N) = a·N^{-b} to extract the scaling exponent.
        """
        log_N = np.log(np.array(N_values, dtype=float))
        log_delta = np.log(np.array(delta_means, dtype=float))
        coeffs = np.polyfit(log_N, log_delta, 1)
        b = -coeffs[0]
        a = np.exp(coeffs[1])

        predicted = np.polyval(coeffs, log_N)
        ss_res = np.sum((log_delta - predicted)**2)
        ss_tot = np.sum((log_delta - np.mean(log_delta))**2)
        r_squared = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0

        return a, b, r_squared


# ═══════════════════════════════════════════════════════════════
#  NEAR-RAMANUJAN ANALYSIS
# ═══════════════════════════════════════════════════════════════

class RamanujanAnalysis:
    """
    Test near-Ramanujan property of the W-graph.

    A k-regular graph is Ramanujan if all non-trivial eigenvalues
    satisfy |λ| ≤ 2√(k-1) (Alon-Boppana bound).

    For the W-graph (approximately regular), the deviation from
    Ramanujan should be O(1/√N) by the DRLT spectral gap bound.
    """

    @staticmethod
    def ramanujan_ratio(N, d=D, n_trials=100, seed=42):
        """
        Compute ρ / (2√(k-1)) for the W-graph.

        ρ = max |non-trivial eigenvalue| of W adjacency
        k = average degree
        Ramanujan ⟺ ratio ≤ 1.
        """
        rng = np.random.RandomState(seed)
        ratios = []
        for _ in range(n_trials):
            psi = rng.randn(N, d) + 1j * rng.randn(N, d)
            norms = np.linalg.norm(psi, axis=1, keepdims=True)
            psi = psi / norms
            G = psi @ psi.conj().T
            W = np.abs(G)**2 / d
            np.fill_diagonal(W, 0.0)

            eigs = np.linalg.eigvalsh(W)
            eigs_sorted = np.sort(np.abs(eigs))[::-1]

            # Largest eigenvalue ≈ average degree
            k_avg = W.sum(axis=1).mean()
            # Second largest eigenvalue (non-trivial)
            rho = eigs_sorted[1] if len(eigs_sorted) > 1 else 0

            bound = 2.0 * np.sqrt(max(k_avg - 1, 0.01))
            ratios.append(rho / bound)

        return np.array(ratios)
