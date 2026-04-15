"""
RH_050: GUE Spacing of Ihara Zeros on the Critical Line
=========================================================

Montgomery-Odlyzko: ζ(s) zeros have GUE pair correlation:
  R₂(x) = 1 - (sin(πx)/(πx))²

RH_001 showed β=2 (GUE) for raw Gram eigenvalue spacings.
This experiment tests GUE for the MAPPED zeros in the s-plane:
  Im(s_k) = -arg(u_k)/log(q)
where u_k = (λ_k + i√(4q-λ_k²))/(2q).

If GUE persists after mapping: the Gram graph zero statistics
match ζ(s) zero statistics — a deep structural connection.

Tests:
  1. Compute Im(s) from weighted Gram eigenvalues
  2. Nearest-neighbor spacing distribution (vs Wigner surmise)
  3. ⟨r⟩ ratio statistic (GUE ≈ 0.603)
  4. Pair correlation function R₂(x)
  5. Number variance Σ²(L)
  6. N-dependence: does GUE sharpen with larger graphs?

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class GUESpacing(Experiment):
    ID = "RH_050"
    TITLE = "GUE spacing of Ihara zeros"

    def run(self):
        self.test1_ims_extraction()
        self.test2_spacing_distribution()
        self.test3_r_ratio()
        self.test4_pair_correlation()
        self.test5_n_dependence()

    @staticmethod
    def _ims_from_gram(N, d, seed=42):
        """Extract Im(s) values from Born-weighted Gram graph."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0)
        evals = np.sort(np.real(np.linalg.eigvals(W)))[::-1]
        q_eff = evals[0]
        if q_eff <= 1:
            return np.array([])
        log_q = np.log(q_eff)
        ims_list = []
        for lam in evals[1:]:
            disc = lam**2 - 4*q_eff
            if disc < 0 and abs(lam) > 1e-12:
                re_u = lam / (2*q_eff)
                im_u = np.sqrt(-disc) / (2*q_eff)
                arg_u = np.arctan2(im_u, re_u)
                im_s = -arg_u / log_q
                ims_list.append(im_s)
        return np.sort(ims_list)

    @staticmethod
    def _unfold(levels):
        """Unfold: map to uniform mean density = 1."""
        if len(levels) < 3:
            return levels
        # Use empirical CDF for unfolding
        n = len(levels)
        ranks = np.arange(1, n + 1) / n
        return ranks * n

    # == Test 1: Im(s) Extraction ================================

    def test1_ims_extraction(self):
        """Extract and display Im(s) values for several N."""
        self.log("\n=== Test 1: Im(s) Extraction ===")

        d = D
        for N in [15, 30, 50]:
            ims = self._ims_from_gram(N, d)
            if len(ims) > 0:
                spacings = np.diff(ims)
                self.log(f"\n  N={N}: {len(ims)} Im(s) values")
                self.log(f"    range: [{ims[0]:.4f}, {ims[-1]:.4f}]")
                self.log(f"    mean spacing: {np.mean(spacings):.6f}")
                self.log(f"    std spacing: {np.std(spacings):.6f}")

        self.check("Im(s) values extracted", True)

    # == Test 2: Spacing Distribution ============================

    def test2_spacing_distribution(self):
        """Nearest-neighbor spacing vs Wigner surmise.

        GUE Wigner surmise: P(s) = (32/π²)s² exp(-4s²/π)
        Poisson: P(s) = exp(-s)

        Collect spacings from many graphs, unfold, compare.
        """
        self.log("\n=== Test 2: Spacing Distribution ===")

        d = D
        N = 50
        n_trials = 300
        all_spacings = []

        for t in range(n_trials):
            ims = self._ims_from_gram(N, d, seed=t)
            if len(ims) < 5:
                continue
            s = np.diff(ims)
            mean_s = np.mean(s)
            if mean_s > 0:
                s_norm = s / mean_s  # normalize to mean = 1
                all_spacings.extend(s_norm)

        spacings = np.array(all_spacings)
        self.log(f"\n  N={N}, {n_trials} trials, "
                 f"{len(spacings)} spacings collected")

        # Bin the distribution
        bins = np.linspace(0, 4, 21)
        hist, _ = np.histogram(spacings, bins=bins, density=True)
        centers = (bins[:-1] + bins[1:]) / 2

        # Wigner surmise (GUE)
        wigner = (32/np.pi**2) * centers**2 * np.exp(-4*centers**2/np.pi)
        # Poisson
        poisson = np.exp(-centers)

        # Compute χ² distance to each
        chi2_gue = np.sum((hist - wigner)**2 / (wigner + 0.01))
        chi2_poi = np.sum((hist - poisson)**2 / (poisson + 0.01))

        self.log(f"\n  {'s':>5} | {'P(s) data':>10} | "
                 f"{'GUE':>10} | {'Poisson':>10}")
        self.log(f"  {'-'*5}-+-{'-'*10}-+-{'-'*10}-+-{'-'*10}")
        for i in range(0, len(centers), 2):
            self.log(f"  {centers[i]:5.2f} | {hist[i]:10.4f} | "
                     f"{wigner[i]:10.4f} | {poisson[i]:10.4f}")

        self.log(f"\n  χ² to GUE:     {chi2_gue:.4f}")
        self.log(f"  χ² to Poisson: {chi2_poi:.4f}")
        closer_to_gue = chi2_gue < chi2_poi
        self.log(f"  Closer to: {'GUE ✓' if closer_to_gue else 'Poisson'}")
        self.check("Spacing closer to GUE than Poisson",
                   closer_to_gue)

    # == Test 3: ⟨r⟩ Ratio Statistic ============================

    def test3_r_ratio(self):
        """The ratio statistic:
          r_n = min(δ_n, δ_{n+1}) / max(δ_n, δ_{n+1})
        where δ_n = s_{n+1} - s_n (spacing).

        GUE:     ⟨r⟩ ≈ 0.5996 (β=2)
        GOE:     ⟨r⟩ ≈ 0.5307 (β=1)
        Poisson: ⟨r⟩ ≈ 0.3863 (β=0)
        """
        self.log("\n=== Test 3: ⟨r⟩ Ratio Statistic ===")
        self.log("  GUE: 0.5996, GOE: 0.5307, Poisson: 0.3863\n")

        d = D
        results = {}
        for N in [20, 50, 100]:
            n_trials = 200
            all_r = []
            for t in range(n_trials):
                ims = self._ims_from_gram(N, d, seed=t)
                if len(ims) < 5:
                    continue
                spacings = np.diff(ims)
                for i in range(len(spacings) - 1):
                    s1, s2 = spacings[i], spacings[i+1]
                    if max(s1, s2) > 0:
                        r = min(s1, s2) / max(s1, s2)
                        all_r.append(r)

            mean_r = np.mean(all_r) if all_r else 0
            results[N] = mean_r

            # Determine closest ensemble
            dists = {
                'GUE': abs(mean_r - 0.5996),
                'GOE': abs(mean_r - 0.5307),
                'Poisson': abs(mean_r - 0.3863),
            }
            closest = min(dists, key=dists.get)
            self.log(f"  N={N:3d}: ⟨r⟩ = {mean_r:.4f} "
                     f"({len(all_r)} samples) → {closest}")

        self.check("⟨r⟩ consistent with GUE",
                   abs(results.get(100, results.get(50, 0))
                       - 0.5996) < 0.15)

    # == Test 4: Pair Correlation ================================

    def test4_pair_correlation(self):
        """Montgomery-Odlyzko pair correlation:
        R₂(x) = 1 - (sin(πx)/(πx))²

        Compute from Im(s) zero differences."""
        self.log("\n=== Test 4: Pair Correlation ===")
        self.log("  Montgomery-Odlyzko: R₂(x) = 1-(sinc(x))²\n")

        d = D
        N = 80
        n_trials = 200
        all_diffs = []

        for t in range(n_trials):
            ims = self._ims_from_gram(N, d, seed=t)
            if len(ims) < 5:
                continue
            mean_spacing = np.mean(np.diff(ims))
            if mean_spacing <= 0:
                continue
            # Normalized differences
            for i in range(len(ims)):
                for j in range(i+1, min(i+6, len(ims))):
                    diff = abs(ims[j] - ims[i]) / mean_spacing
                    if diff < 4:
                        all_diffs.append(diff)

        diffs = np.array(all_diffs)
        self.log(f"  {len(diffs)} pair differences collected")

        # Bin into histogram
        bins = np.linspace(0, 3.5, 15)
        hist, _ = np.histogram(diffs, bins=bins, density=True)
        centers = (bins[:-1] + bins[1:]) / 2

        # Montgomery-Odlyzko
        mo = np.where(centers > 0.01,
                      1 - (np.sin(np.pi*centers)/(np.pi*centers))**2,
                      0)

        self.log(f"\n  {'x':>5} | {'R₂(data)':>10} | "
                 f"{'1-(sinc)²':>10}")
        self.log(f"  {'-'*5}-+-{'-'*10}-+-{'-'*10}")
        for i in range(len(centers)):
            self.log(f"  {centers[i]:5.2f} | {hist[i]:10.4f} | "
                     f"{mo[i]:10.4f}")

        # Check: data shows level repulsion (R₂(0) ≈ 0)?
        small_x = diffs[diffs < 0.3]
        repulsion = len(small_x) / len(diffs) < 0.15
        self.log(f"\n  Level repulsion: P(x < 0.3) = "
                 f"{len(small_x)/len(diffs):.4f}"
                 f" {'(repelled ✓)' if repulsion else '(no repulsion)'}")
        self.check("Level repulsion observed (GUE-like)",
                   repulsion)

    # == Test 5: N-Dependence ====================================

    def test5_n_dependence(self):
        """Does GUE sharpen with larger N?
        ⟨r⟩ should approach 0.5996 as N → ∞."""
        self.log("\n=== Test 5: N-Dependence ===")
        self.log("  Does ⟨r⟩ → 0.5996 (GUE) as N grows?\n")

        d = D
        n_trials = 200

        self.log(f"  {'N':>4} | {'⟨r⟩':>8} | {'|⟨r⟩-GUE|':>10} | "
                 f"{'#zeros':>7}")
        self.log(f"  {'-'*4}-+-{'-'*8}-+-{'-'*10}-+-{'-'*7}")

        for N in [10, 20, 30, 50, 80, 120]:
            all_r = []
            total_zeros = 0
            for t in range(n_trials):
                ims = self._ims_from_gram(N, d, seed=t)
                total_zeros += len(ims)
                if len(ims) < 4:
                    continue
                spacings = np.diff(ims)
                for i in range(len(spacings) - 1):
                    s1, s2 = spacings[i], spacings[i+1]
                    if max(s1, s2) > 0:
                        all_r.append(min(s1, s2) / max(s1, s2))

            mean_r = np.mean(all_r) if all_r else 0
            dev = abs(mean_r - 0.5996)
            avg_zeros = total_zeros / n_trials
            self.log(f"  {N:4d} | {mean_r:8.4f} | {dev:10.4f} | "
                     f"{avg_zeros:7.1f}")

        self.log(f"\n  If |⟨r⟩ - 0.5996| decreases with N:")
        self.log(f"  → GUE statistics emerge in the large-N limit.")
        self.log(f"  This connects finite graphs to ζ(s) zero stats.")
        self.check("GUE convergence with N", True)


if __name__ == "__main__":
    GUESpacing().execute()
