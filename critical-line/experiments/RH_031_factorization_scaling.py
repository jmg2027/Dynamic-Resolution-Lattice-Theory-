"""
RH_031: (2,3) Factorization — Real or Artifact?
=================================================

RH_030 found Tr(B^6) phase = Tr(B^2)*Tr(B^3) phase EXACTLY (diff=0).
This could be:
  (a) A deep structural fact (additive atoms 2,3 → perfect factorization)
  (b) A small-N artifact (rank ≤ 5 forces structure at N=8)

Tests:
  1. Scale N from 6 to 30 — does (2,3) stay perfect?
  2. All factorization pairs (a,b) with ab ≤ 12 across N
  3. Compare d=5 vs d=3 vs d=10 — is it d-dependent?
  4. Statistical significance: p-value of (2,3) diff = 0

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class FactorizationScaling(Experiment):
    ID = "RH_031"
    TITLE = "Factorization scaling with N"

    def run(self):
        self.test1_23_vs_N()
        self.test2_all_pairs()
        self.test3_d_dependence()
        self.test4_significance()

    @staticmethod
    def _make_gram(N, d=D, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        return psi @ psi.conj().T

    @staticmethod
    def _edge_adjacency(G):
        N = G.shape[0]
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_edges = len(edges)
        edge_idx = {e: idx for idx, e in enumerate(edges)}
        B = np.zeros((n_edges, n_edges), dtype=complex)
        for idx1, (i, j) in enumerate(edges):
            for k in range(N):
                if k != i and k != j:
                    idx2 = edge_idx.get((j, k))
                    if idx2 is not None:
                        B[idx1, idx2] = G[j, k]
        return B, edges

    @staticmethod
    def _phase_diff(B, a, b):
        """Phase difference: arg(Tr(B^{ab})) - arg(Tr(B^a)) - arg(Tr(B^b))."""
        Ba = np.linalg.matrix_power(B, a)
        Bb = np.linalg.matrix_power(B, b)
        Bab = np.linalg.matrix_power(B, a * b)
        pa = np.angle(np.trace(Ba))
        pb = np.angle(np.trace(Bb))
        pab = np.angle(np.trace(Bab))
        diff = (pab - pa - pb + np.pi) % (2 * np.pi) - np.pi
        return abs(diff)

    # -- Test 1: (2,3) factorization vs N ------------------------

    def test1_23_vs_N(self):
        """Does (2,3) perfect factorization survive larger N?"""
        self.log("\n=== Test 1: (2,3) factorization vs N ===")

        N_values = [6, 8, 10, 12, 15, 20]
        n_trials = 100

        self.log(f"\n  {'N':>4} | {'mean |diff|':>12} | "
                 f"{'std':>8} | {'min':>8} | {'max':>8}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*8}-+-{'-'*8}-+-{'-'*8}")

        for N in N_values:
            diffs = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                B, _ = self._edge_adjacency(G)
                diffs.append(self._phase_diff(B, 2, 3))

            self.log(f"  {N:4d} | {np.mean(diffs):12.6f} | "
                     f"{np.std(diffs):8.6f} | {np.min(diffs):8.6f} | "
                     f"{np.max(diffs):8.6f}")

        self.check("(2,3) scaling measured", True)

    # -- Test 2: All factorization pairs --------------------------

    def test2_all_pairs(self):
        """Compare all (a,b) pairs at fixed N=10."""
        self.log("\n=== Test 2: All factorization pairs (N=10) ===")

        N = 10
        n_trials = 100
        pairs = [(2,2), (2,3), (2,4), (2,5), (2,6),
                 (3,3), (3,4), (3,5), (4,4)]

        self.log(f"\n  {'(a,b)':>7} | {'ab':>4} | {'mean |diff|':>12} | "
                 f"{'ratio/random':>13} | note")
        self.log(f"  {'-'*7}-+-{'-'*4}-+-{'-'*12}-+-{'-'*13}-+-----")

        from math import gcd
        for a, b in pairs:
            diffs = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                B, _ = self._edge_adjacency(G)
                diffs.append(self._phase_diff(B, a, b))

            mean_d = np.mean(diffs)
            ratio = mean_d / (np.pi / 2)
            g = gcd(a, b)
            note = "atoms" if (a, b) == (2, 3) else \
                   f"gcd={g}" if g > 1 else ""
            self.log(f"  ({a},{b}){' '*(5-len(f'({a},{b})'))} | "
                     f"{a*b:4d} | {mean_d:12.6f} | {ratio:13.4f} | {note}")

        self.check("All pairs measured", True)

    # -- Test 3: d-dependence -------------------------------------

    def test3_d_dependence(self):
        """Is (2,3) factorization specific to d=5?"""
        self.log("\n=== Test 3: (2,3) factorization vs d ===")

        N = 10
        n_trials = 100
        d_values = [3, 4, 5, 6, 8, 10]

        self.log(f"\n  {'d':>4} | {'(2,3) diff':>12} | {'(2,4) diff':>12} | "
                 f"{'(3,4) diff':>12}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*12}-+-{'-'*12}")

        for d in d_values:
            diffs_23, diffs_24, diffs_34 = [], [], []
            for t in range(n_trials):
                G = self._make_gram(N, d=d, seed=t)
                B, _ = self._edge_adjacency(G)
                diffs_23.append(self._phase_diff(B, 2, 3))
                diffs_24.append(self._phase_diff(B, 2, 4))
                diffs_34.append(self._phase_diff(B, 3, 4))

            marker = " <-- DRLT" if d == 5 else ""
            self.log(f"  {d:4d} | {np.mean(diffs_23):12.6f} | "
                     f"{np.mean(diffs_24):12.6f} | "
                     f"{np.mean(diffs_34):12.6f}{marker}")

        self.check("d-dependence measured", True)

    # -- Test 4: Statistical significance -------------------------

    def test4_significance(self):
        """Is (2,3) diff = 0 statistically significant?
        Compare to null hypothesis: random phases."""
        self.log("\n=== Test 4: Statistical significance ===")

        N = 10
        n_trials = 500

        # Actual Gram (2,3) diffs
        gram_diffs = []
        for t in range(n_trials):
            G = self._make_gram(N, seed=t)
            B, _ = self._edge_adjacency(G)
            gram_diffs.append(self._phase_diff(B, 2, 3))

        # Null: random B matrix (same size, random complex entries)
        null_diffs = []
        for t in range(n_trials):
            rng = np.random.RandomState(t + 10000)
            n_edges = N * (N - 1)
            B_rand = (rng.randn(n_edges, n_edges) +
                      1j * rng.randn(n_edges, n_edges)) / np.sqrt(n_edges)
            null_diffs.append(self._phase_diff(B_rand, 2, 3))

        gram_mean = np.mean(gram_diffs)
        null_mean = np.mean(null_diffs)

        # t-test like comparison
        gram_std = np.std(gram_diffs)
        null_std = np.std(null_diffs)
        se = np.sqrt(gram_std**2/n_trials + null_std**2/n_trials)
        z_score = (null_mean - gram_mean) / se if se > 0 else 0

        self.log(f"\n  Gram (2,3): mean={gram_mean:.6f}, "
                 f"std={gram_std:.6f}")
        self.log(f"  Null (random B): mean={null_mean:.6f}, "
                 f"std={null_std:.6f}")
        self.log(f"  Z-score (Gram < null): {z_score:.2f}")
        self.log(f"  (Z > 3 means significant at 99.9%)")

        significant = z_score > 3
        self.log(f"\n  Result: "
                 f"{'SIGNIFICANT' if significant else 'not significant'}")
        self.check("(2,3) factorization is statistically significant",
                   significant)


if __name__ == "__main__":
    FactorizationScaling().execute()
