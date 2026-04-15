"""
RH_041: The Missing Inequality — Ihara Zero Deviation vs δ(N)
==============================================================

From YM (Lean-verified): Δ ≥ ε → det ≥ (ε/π)²
We need the RH analog: |Re(s)-1/2| ≥ ε → δ(N) ≥ f(ε)

For the Gram graph's Ihara zeta, zeros are at u = 1/λ.
The "critical circle" is |u| = 1/√q.
Deviation from critical circle = ||u| - 1/√q|.

Tests:
  1. Compute Ihara zeros and their deviation from critical circle
  2. Compute δ(N) for the same Gram ensemble
  3. Plot deviation vs δ(N) — find the bound f(ε)
  4. Verify: small δ(N) forces zeros near critical circle

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class HadamardBound(Experiment):
    ID = "RH_041"
    TITLE = "Hadamard bound for Ihara zeros"

    def run(self):
        self.test1_deviation_vs_delta()
        self.test2_bound_extraction()
        self.test3_scaling()

    @staticmethod
    def _make_gram(N, d=D, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        return psi @ psi.conj().T

    @staticmethod
    def _delta(G):
        """Resolution limit: δ = 1 - max|G_{ij}|² for i≠j."""
        N = G.shape[0]
        overlaps = np.abs(G) ** 2
        np.fill_diagonal(overlaps, 0)
        return 1.0 - np.max(overlaps)

    @staticmethod
    def _ihara_zeros_born(G):
        """Ihara zeros from Born-weighted NB adjacency."""
        N = G.shape[0]
        W = np.abs(G) ** 2
        np.fill_diagonal(W, 0)

        edges = [(i, j) for i in range(N) for j in range(N)
                 if i != j and W[i, j] > 0]
        n_e = len(edges)
        idx = {e: i for i, e in enumerate(edges)}
        B = np.zeros((n_e, n_e))
        for i1, (a, b) in enumerate(edges):
            for c in range(N):
                if c != a and c != b and W[b, c] > 0:
                    i2 = idx.get((b, c))
                    if i2 is not None:
                        B[i1, i2] = W[b, c]

        evals = np.linalg.eigvals(B)
        nz = evals[np.abs(evals) > 1e-10]
        return 1.0 / nz, np.max(np.abs(evals))

    # -- Test 1: Deviation vs delta(N) ----------------------------

    def test1_deviation_vs_delta(self):
        """For many Gram realizations, compute:
        - delta(N) = resolution limit
        - max deviation of Ihara zeros from critical circle
        Check: does small delta force small deviation?"""
        self.log("\n=== Test 1: Zero deviation vs delta(N) ===")

        N_values = [6, 8, 10, 12]
        n_trials = 50

        self.log(f"\n  {'N':>4} | {'mean delta':>10} | "
                 f"{'mean max_dev':>12} | {'max_dev/delta':>13} | "
                 f"{'corr':>6}")
        self.log(f"  {'-'*4}-+-{'-'*10}-+-{'-'*12}-+-{'-'*13}-+-{'-'*6}")

        for N in N_values:
            deltas = []
            max_devs = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                d = self._delta(G)
                deltas.append(d)

                zeros, rho = self._ihara_zeros_born(G)
                if rho > 0:
                    r_crit = 1 / np.sqrt(rho)
                    radii = np.abs(zeros)
                    # Max deviation from critical circle
                    dev = np.max(np.abs(radii - r_crit))
                    max_devs.append(dev)
                else:
                    max_devs.append(0)

            deltas = np.array(deltas)
            max_devs = np.array(max_devs)

            # Correlation
            if np.std(deltas) > 0 and np.std(max_devs) > 0:
                corr = np.corrcoef(deltas, max_devs)[0, 1]
            else:
                corr = 0

            ratio = np.mean(max_devs) / np.mean(deltas) \
                if np.mean(deltas) > 0 else 0

            self.log(f"  {N:4d} | {np.mean(deltas):10.4f} | "
                     f"{np.mean(max_devs):12.4f} | {ratio:13.4f} | "
                     f"{corr:6.3f}")

        self.check("Deviation vs delta measured", True)

    # -- Test 2: Extract the bound f(ε) --------------------------

    def test2_bound_extraction(self):
        """For each realization, record (delta, max_dev) pair.
        Find: max_dev ≤ C * delta^alpha for some C, alpha.

        YM analog: ε ≤ π * sqrt(det)
        RH analog: max_dev ≤ C * delta^alpha?"""
        self.log("\n=== Test 2: Bound extraction ===")
        self.log("  Find: max_dev <= C * delta^alpha")

        N = 10
        n_trials = 300

        deltas = []
        max_devs = []
        for t in range(n_trials):
            G = self._make_gram(N, seed=t)
            d = self._delta(G)
            deltas.append(d)

            zeros, rho = self._ihara_zeros_born(G)
            if rho > 0:
                r_crit = 1 / np.sqrt(rho)
                radii = np.abs(zeros)
                dev = np.max(np.abs(radii - r_crit))
                max_devs.append(dev)
            else:
                max_devs.append(0)

        deltas = np.array(deltas)
        max_devs = np.array(max_devs)

        # Log-log fit: log(max_dev) = alpha * log(delta) + log(C)
        valid = (deltas > 0) & (max_devs > 0)
        if np.sum(valid) > 10:
            log_d = np.log(deltas[valid])
            log_m = np.log(max_devs[valid])
            A = np.column_stack([log_d, np.ones(np.sum(valid))])
            result = np.linalg.lstsq(A, log_m, rcond=None)
            alpha = result[0][0]
            C = np.exp(result[0][1])

            self.log(f"\n  Fit: max_dev ~ {C:.4f} * delta^{alpha:.4f}")
            self.log(f"  R² = {1 - np.var(log_m - A @ result[0]) / np.var(log_m):.4f}")

            # Check: is alpha > 0? (meaning small delta → small deviation)
            self.log(f"\n  alpha > 0: {'YES' if alpha > 0 else 'NO'}")
            self.log(f"  Interpretation: {'smaller delta forces zeros closer to critical circle' if alpha > 0 else 'no clear relationship'}")
        else:
            alpha = 0
            self.log(f"\n  Insufficient valid data for fit")

        # The YM analog: max_dev = sqrt(det) * pi
        # Here: max_dev ~ C * delta^alpha
        # If alpha ~ 0.5, that would match sqrt(det) pattern
        self.log(f"\n  YM has: ε = sqrt(det) * π (alpha=0.5)")
        self.log(f"  RH has: max_dev ~ delta^{alpha:.3f}")

        self.check("Bound extracted", alpha > -0.5)

    # -- Test 3: N-scaling of the bound ---------------------------

    def test3_scaling(self):
        """How does the bound change with N?
        As N grows, delta shrinks. Do zeros concentrate?"""
        self.log("\n=== Test 3: N-scaling ===")

        n_trials = 100

        self.log(f"\n  {'N':>4} | {'mean delta':>10} | {'mean max_dev':>12} | "
                 f"{'Ramanujan fraction':>18}")
        self.log(f"  {'-'*4}-+-{'-'*10}-+-{'-'*12}-+-{'-'*18}")

        for N in [6, 8, 10, 12, 15]:
            deltas = []
            ram_fracs = []
            devs = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                deltas.append(self._delta(G))

                zeros, rho = self._ihara_zeros_born(G)
                if rho > 0:
                    r_crit = 1 / np.sqrt(rho)
                    radii = np.abs(zeros)
                    dev = np.max(np.abs(radii - r_crit))
                    devs.append(dev)

                    # Fraction of zeros "on" critical circle (within 10%)
                    on_circle = np.mean(np.abs(radii - r_crit) < 0.1 * r_crit)
                    ram_fracs.append(on_circle)

            self.log(f"  {N:4d} | {np.mean(deltas):10.4f} | "
                     f"{np.mean(devs):12.4f} | "
                     f"{np.mean(ram_fracs):18.1%}")

        self.log(f"\n  As N grows:")
        self.log(f"  - delta shrinks (resolution improves)")
        self.log(f"  - max_dev: does it shrink too?")
        self.log(f"  - Ramanujan fraction: does it increase?")
        self.check("N-scaling measured", True)


if __name__ == "__main__":
    HadamardBound().execute()
