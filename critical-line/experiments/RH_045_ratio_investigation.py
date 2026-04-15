"""
RH_045: The Ratio pi(p^2)/pi(p) on Weighted Gram
==================================================

RH_044 found pi(9)/pi(3) ~ 3 = n_S on Born-weighted graph.
Is this n_S, or coincidence? Check across d and N.

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D, N_S, N_T


class RatioInvestigation(Experiment):
    ID = "RH_045"
    TITLE = "Cycle ratio investigation"

    def run(self):
        self.test1_ratio_vs_d()
        self.test2_ratio_vs_N()
        self.test3_higher_powers()

    @staticmethod
    def _weighted_nb(N, d, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G) ** 2
        np.fill_diagonal(W, 0)
        edges = [(i, j) for i in range(N) for j in range(N)
                 if i != j and W[i, j] > 0]
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

    @staticmethod
    def _mu(n):
        if n == 1: return 1
        temp, factors = n, []
        for p in range(2, int(n**0.5) + 2):
            if temp % p == 0:
                c = 0
                while temp % p == 0: temp //= p; c += 1
                if c > 1: return 0
                factors.append(p)
        if temp > 1: factors.append(temp)
        return (-1)**len(factors)

    @staticmethod
    def _divisors(n):
        return [d for d in range(1, n+1) if n % d == 0]

    @staticmethod
    def _compute_pi(B, max_len):
        W = {}
        Bk = np.eye(B.shape[0])
        for n in range(1, max_len + 1):
            Bk = Bk @ B
            W[n] = np.real(np.trace(Bk))
        pi_w = {}
        for n in range(1, max_len + 1):
            total = sum(RatioInvestigation._mu(n // d) * W.get(d, 0)
                        for d in RatioInvestigation._divisors(n))
            pi_w[n] = total / n
        return pi_w

    def test1_ratio_vs_d(self):
        """Is pi(9)/pi(3) = 3 specific to d=5?"""
        self.log("\n=== Test 1: pi(9)/pi(3) vs d ===")
        self.log(f"  DRLT: n_S = {N_S}, n_T = {N_T}")

        N = 10
        n_trials = 100

        self.log(f"\n  {'d':>4} | {'pi(9)/pi(3)':>12} | {'std':>8} | "
                 f"{'d-1':>6} | {'d':>4}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*8}-+-{'-'*6}-+-{'-'*4}")

        for d in [2, 3, 4, 5, 6, 8, 10, 15, 20]:
            ratios = []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                pi_w = self._compute_pi(B, 10)
                if abs(pi_w.get(3, 0)) > 1e-10:
                    ratios.append(pi_w[9] / pi_w[3])
            if ratios:
                m = np.mean(ratios)
                s = np.std(ratios)
                self.log(f"  {d:4d} | {m:12.4f} | {s:8.4f} | "
                         f"{d-1:6d} | {d:4d}")

        self.check("Ratio vs d measured", True)

    def test2_ratio_vs_N(self):
        """Does the ratio depend on N?"""
        self.log("\n=== Test 2: pi(9)/pi(3) vs N (d=5) ===")

        d = D
        n_trials = 100

        self.log(f"\n  {'N':>4} | {'pi(9)/pi(3)':>12} | {'std':>8}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*8}")

        for N in [6, 8, 10, 12, 15]:
            ratios = []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                pi_w = self._compute_pi(B, 10)
                if abs(pi_w.get(3, 0)) > 1e-10:
                    ratios.append(pi_w[9] / pi_w[3])
            if ratios:
                self.log(f"  {N:4d} | {np.mean(ratios):12.4f} | "
                         f"{np.std(ratios):8.4f}")

        self.check("Ratio vs N measured", True)

    def test3_higher_powers(self):
        """Multiple pi ratios to look for DRLT constants."""
        self.log("\n=== Test 3: Various pi ratios (d=5, N=12) ===")

        N = 12
        d = D
        n_trials = 100

        pairs = [
            ("pi(9)/pi(3)", 9, 3),
            ("pi(6)/pi(3)", 6, 3),
            ("pi(6)/pi(2)", 6, 2),
            ("pi(10)/pi(5)", 10, 5),
            ("pi(12)/pi(3)", 12, 3),
            ("pi(12)/pi(4)", 12, 4),
            ("pi(12)/pi(6)", 12, 6),
        ]

        self.log(f"\n  {'ratio':>16} | {'mean':>10} | {'std':>8} | "
                 f"{'nearest':>8}")
        self.log(f"  {'-'*16}-+-{'-'*10}-+-{'-'*8}-+-{'-'*8}")

        for label, num, den in pairs:
            ratios = []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                pi_w = self._compute_pi(B, 12)
                if abs(pi_w.get(den, 0)) > 1e-10:
                    ratios.append(pi_w[num] / pi_w[den])
            if ratios:
                m = np.mean(ratios)
                self.log(f"  {label:>16} | {m:10.4f} | "
                         f"{np.std(ratios):8.4f} | {round(m):8d}")

        self.check("Higher ratios measured", True)


if __name__ == "__main__":
    RatioInvestigation().execute()
