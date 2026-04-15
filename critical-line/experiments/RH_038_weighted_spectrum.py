"""
RH_038: Weighted Gram Spectrum — How d Enters
===============================================

K_N unweighted has 4 eigenvalues: {N-2, 1, -1/2, -1}.
The Gram graph has Born weights |G_{ij}|^2 ~ 1/d.
How does weighting change the spectrum?

Key question: does lambda_2 = 1 survive weighting?
If yes: error structure unchanged, d only scales q.
If no: d creates NEW eigenvalue structure.

Tests:
  1. Weighted NB spectrum for various d
  2. Does the 4-eigenvalue structure survive?
  3. How does lambda_2 depend on d?
  4. The ratio lambda_1/lambda_2 vs d

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class WeightedSpectrum(Experiment):
    ID = "RH_038"
    TITLE = "Weighted Gram NB spectrum"

    def run(self):
        self.test1_weighted_spectrum()
        self.test2_four_eigenvalues()
        self.test3_lambda2_vs_d()
        self.test4_ramanujan_ratio()

    @staticmethod
    def _weighted_nb(N, d, seed=42):
        """NB adjacency with Born weights |G_{ij}|^2."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G) ** 2
        np.fill_diagonal(W, 0)

        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_e = len(edges)
        idx = {e: i for i, e in enumerate(edges)}
        B = np.zeros((n_e, n_e))
        for i1, (a, b) in enumerate(edges):
            for c in range(N):
                if c != a and c != b:
                    i2 = idx.get((b, c))
                    if i2 is not None:
                        B[i1, i2] = W[b, c]
        return B

    # -- Test 1: Weighted spectrum --------------------------------

    def test1_weighted_spectrum(self):
        """Full spectrum of Born-weighted NB adjacency."""
        self.log("\n=== Test 1: Weighted NB spectrum ===")

        N = 10
        for d in [3, 5, 10, 50]:
            B = self._weighted_nb(N, d)
            evals = np.real(np.linalg.eigvals(B))
            evals_sort = np.sort(evals)[::-1]

            self.log(f"\n  N={N}, d={d}:")
            self.log(f"  Top 5: {evals_sort[:5].round(4)}")
            self.log(f"  Bottom 3: {evals_sort[-3:].round(4)}")

            # Count distinct eigenvalues (within tolerance)
            rounded = np.round(evals, 2)
            n_distinct = len(np.unique(rounded))
            self.log(f"  Distinct eigenvalues (tol=0.01): {n_distinct}")

        self.check("Weighted spectra computed", True)

    # -- Test 2: Does 4-eigenvalue structure survive? -------------

    def test2_four_eigenvalues(self):
        """Unweighted K_N has exactly 4 distinct eigenvalues.
        Does this structure survive Born weighting?"""
        self.log("\n=== Test 2: Eigenvalue clustering ===")
        self.log("  Unweighted: 4 distinct values")
        self.log("  Weighted: how many clusters?")

        N = 10
        n_trials = 30

        for d in [3, 5, 10]:
            cluster_counts = []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                evals = np.real(np.linalg.eigvals(B))
                # Count clusters using histogram
                hist, _ = np.histogram(evals, bins=50)
                n_peaks = np.sum(hist > 0)
                cluster_counts.append(n_peaks)

            self.log(f"\n  d={d}: mean clusters = {np.mean(cluster_counts):.1f}"
                     f" (unweighted: 4)")

        self.log(f"\n  If clusters >> 4: weighting BREAKS the structure")
        self.log(f"  If clusters ~ 4: structure survives (just shifted)")
        self.check("Clustering analyzed", True)

    # -- Test 3: lambda_2 vs d -----------------------------------

    def test3_lambda2_vs_d(self):
        """How does the second eigenvalue depend on d?"""
        self.log("\n=== Test 3: lambda_2 vs d ===")

        N = 10
        n_trials = 50

        self.log(f"\n  {'d':>4} | {'lam1':>8} | {'lam2':>8} | "
                 f"{'lam2/lam1':>10} | {'1/d':>6} | {'lam1*d':>8}")
        self.log(f"  {'-'*4}-+-{'-'*8}-+-{'-'*8}-+-{'-'*10}-+-"
                 f"{'-'*6}-+-{'-'*8}")

        for d in [2, 3, 4, 5, 6, 8, 10, 15, 20, 50]:
            lam1s, lam2s = [], []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                evals = np.sort(np.real(np.linalg.eigvals(B)))[::-1]
                lam1s.append(evals[0])
                lam2s.append(evals[1])

            l1 = np.mean(lam1s)
            l2 = np.mean(lam2s)
            ratio = l2 / l1 if l1 > 0 else 0

            self.log(f"  {d:4d} | {l1:8.4f} | {l2:8.4f} | "
                     f"{ratio:10.4f} | {1/d:6.4f} | {l1*d:8.4f}")

        self.log(f"\n  If lam1*d ~ const: lam1 = (N-2)/d")
        self.log(f"  If lam2/lam1 ~ const: same structure, just scaled")
        self.check("lambda_2 vs d measured", True)

    # -- Test 4: Ramanujan ratio ---------------------------------

    def test4_ramanujan_ratio(self):
        """Is the weighted graph Ramanujan?
        Ramanujan: lam2 <= 2*sqrt(lam1).
        Ratio lam2 / (2*sqrt(lam1)) < 1 means Ramanujan."""
        self.log("\n=== Test 4: Ramanujan ratio ===")

        N = 10
        n_trials = 50

        self.log(f"\n  {'d':>4} | {'lam2/(2*sqrt(lam1))':>20} | "
                 f"{'Ramanujan?':>10}")
        self.log(f"  {'-'*4}-+-{'-'*20}-+-{'-'*10}")

        for d in [3, 5, 8, 10, 20, 50]:
            ratios = []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                evals = np.sort(np.real(np.linalg.eigvals(B)))[::-1]
                l1, l2 = evals[0], evals[1]
                if l1 > 0:
                    ratios.append(l2 / (2 * np.sqrt(l1)))

            mean_r = np.mean(ratios)
            is_ram = "YES" if mean_r < 1 else "NO"
            self.log(f"  {d:4d} | {mean_r:20.4f} | {is_ram:>10}")

        self.log(f"\n  Ramanujan for all d means error ~ sqrt(lam1)")
        self.log(f"  = sqrt((N-2)/d) ~ sqrt(q/d)")
        self.log(f"  -> d TIGHTENS the Ramanujan bound")
        self.check("Ramanujan check done", True)


if __name__ == "__main__":
    WeightedSpectrum().execute()
