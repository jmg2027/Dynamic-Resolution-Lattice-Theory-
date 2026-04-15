"""
RH_046: The u → s Map — Connecting Graph RH to Classical RH
=============================================================

The structural parallel:
  Z_G(u) = prod_k (1 - u * lambda_k)^{-1}   (graph Euler product)
  zeta(s) = prod_p (1 - p^{-s})^{-1}          (Riemann Euler product)

The map: u = q^{-s} where q = spectral radius of B.
Under this map:
  |u| = 1/sqrt(q)  <==>  Re(s) = 1/2
  Ramanujan bound   <==>  Riemann Hypothesis

Question: Does this map work for the WEIGHTED Gram graph?
If Z_G zeros are at |u_k|, then s_k = -log|u_k| / log(q).
If all |u_k| = 1/sqrt(q), then all Re(s_k) = 1/2.

Tests:
  1. Compute Z_G zeros and map to s-plane
  2. Check: Re(s_k) = 1/2 for unweighted K_N?
  3. Check: Re(s_k) near 1/2 for weighted Gram?
  4. How does the spread of Re(s_k) relate to delta(N)?

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class UtoSMap(Experiment):
    ID = "RH_046"
    TITLE = "u to s map graph-to-Riemann"

    def run(self):
        self.test1_unweighted_s_plane()
        self.test2_weighted_s_plane()
        self.test3_spread_vs_delta()

    @staticmethod
    def _unweighted_nb(N):
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_e = len(edges)
        idx = {e: i for i, e in enumerate(edges)}
        A = np.zeros((n_e, n_e), dtype=float)
        for i1, (a, b) in enumerate(edges):
            for c in range(N):
                if c != a and c != b:
                    i2 = idx.get((b, c))
                    if i2 is not None:
                        A[i1, i2] = 1.0
        return A

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
    def _zeros_to_s(B):
        """Map eigenvalues of B to s-plane via u = q^{-s}.
        s = -log(u) / log(q) = -log(1/lambda) / log(q)
          = log(lambda) / log(q)
        Re(s) = log|lambda| / log(q)
        """
        evals = np.linalg.eigvals(B)
        q = np.max(np.abs(evals))
        if q <= 1:
            return None, None, q

        nz = evals[np.abs(evals) > 1e-10]
        log_q = np.log(q)
        s_values = np.log(nz) / log_q  # complex s
        re_s = np.real(s_values)
        return re_s, s_values, q

    # -- Test 1: Unweighted K_N → s-plane -------------------------

    def test1_unweighted_s_plane(self):
        """For K_N unweighted, eigenvalues are {q, 1, -1/2, -1}.
        Map to s:
          lambda = q → s = 1 (trivial zero)
          lambda = 1 → s = 0
          lambda = -1/2 → s = log(1/2)/log(q) + i*pi/log(q)
          lambda = -1 → s = i*pi/log(q)

        The "non-trivial" zeros have Re(s) determined by |lambda|.
        For |lambda| = 1: Re(s) = 0.
        For |lambda| = sqrt(q): Re(s) = 1/2 (critical line!).
        """
        self.log("\n=== Test 1: Unweighted K_N in s-plane ===")

        for N in [8, 10, 12]:
            A = self._unweighted_nb(N)
            q = N - 2

            # Known eigenvalues
            evals_known = {
                'q': float(q),
                '1': 1.0,
                '-1/2': -0.5,
                '-1': -1.0,
            }

            self.log(f"\n  K_{N} (q = {q}):")
            self.log(f"  {'lambda':>8} | {'|lambda|':>8} | "
                     f"{'Re(s)':>8} | {'1/2?':>6}")
            self.log(f"  {'-'*8}-+-{'-'*8}-+-{'-'*8}-+-{'-'*6}")

            for name, lam in evals_known.items():
                abs_lam = abs(lam)
                if abs_lam > 0:
                    re_s = np.log(abs_lam) / np.log(q)
                else:
                    re_s = float('-inf')
                is_half = "YES" if abs(re_s - 0.5) < 0.01 else ""
                self.log(f"  {name:>8} | {abs_lam:8.4f} | "
                         f"{re_s:8.4f} | {is_half:>6}")

            # Ramanujan bound: |lambda| <= 2*sqrt(q) → Re(s) >= ?
            ram_bound = 2 * np.sqrt(q)
            re_s_ram = np.log(ram_bound) / np.log(q)
            self.log(f"\n  Ramanujan: |lam| <= 2*sqrt(q) = {ram_bound:.2f}")
            self.log(f"  → Re(s) <= {re_s_ram:.4f}")
            self.log(f"  (For lambda = sqrt(q): Re(s) = 0.5000 exactly)")

        self.check("Unweighted s-plane computed", True)

    # -- Test 2: Weighted Gram → s-plane --------------------------

    def test2_weighted_s_plane(self):
        """Map weighted Gram eigenvalues to s-plane.
        Check: how close are Re(s_k) to 1/2?"""
        self.log("\n=== Test 2: Weighted Gram in s-plane ===")

        N = 10
        n_trials = 50

        for d in [3, 5, 10]:
            all_re_s = []
            for t in range(n_trials):
                B = self._weighted_nb(N, d, seed=t)
                re_s, _, q = self._zeros_to_s(B)
                if re_s is not None:
                    # Exclude trivial (Re(s) ~ 1) and near-zero
                    nontrivial = re_s[(re_s > 0.05) & (re_s < 0.95)]
                    all_re_s.extend(nontrivial)

            if all_re_s:
                all_re_s = np.array(all_re_s)
                self.log(f"\n  d={d}: {len(all_re_s)} non-trivial Re(s)")
                self.log(f"  Mean Re(s) = {np.mean(all_re_s):.4f}")
                self.log(f"  Median Re(s) = {np.median(all_re_s):.4f}")
                self.log(f"  Std Re(s) = {np.std(all_re_s):.4f}")
                self.log(f"  Fraction |Re(s)-0.5| < 0.1: "
                         f"{np.mean(np.abs(all_re_s - 0.5) < 0.1):.1%}")

        self.check("Weighted s-plane computed", True)

    # -- Test 3: Spread of Re(s) vs delta(N) ----------------------

    def test3_spread_vs_delta(self):
        """The key test: does delta(N) control the spread of Re(s)?
        If spread(Re(s)) ~ f(delta), then:
          delta → 0 forces Re(s) → 1/2 (RH)."""
        self.log("\n=== Test 3: Spread of Re(s) vs delta(N) ===")

        d = D
        n_trials = 100

        self.log(f"\n  {'N':>4} | {'mean delta':>10} | "
                 f"{'mean |Re(s)-0.5|':>18} | {'corr':>6}")
        self.log(f"  {'-'*4}-+-{'-'*10}-+-{'-'*18}-+-{'-'*6}")

        for N in [6, 8, 10, 12]:
            deltas = []
            spreads = []
            for t in range(n_trials):
                # Delta
                rng = np.random.RandomState(t)
                psi = rng.randn(N, d) + 1j * rng.randn(N, d)
                psi /= np.linalg.norm(psi, axis=1, keepdims=True)
                G = psi @ psi.conj().T
                overlaps = np.abs(G) ** 2
                np.fill_diagonal(overlaps, 0)
                delta = 1.0 - np.max(overlaps)
                deltas.append(delta)

                # Re(s) spread
                B = self._weighted_nb(N, d, seed=t)
                re_s, _, q = self._zeros_to_s(B)
                if re_s is not None:
                    nontrivial = re_s[(re_s > 0.05) & (re_s < 0.95)]
                    if len(nontrivial) > 0:
                        spread = np.mean(np.abs(nontrivial - 0.5))
                        spreads.append(spread)
                    else:
                        spreads.append(0)
                else:
                    spreads.append(0)

            deltas = np.array(deltas)
            spreads = np.array(spreads)
            valid = spreads > 0
            if np.sum(valid) > 10:
                corr = np.corrcoef(deltas[valid], spreads[valid])[0, 1]
            else:
                corr = 0

            self.log(f"  {N:4d} | {np.mean(deltas):10.4f} | "
                     f"{np.mean(spreads):18.4f} | {corr:6.3f}")

        self.log(f"\n  If corr > 0: large delta → large spread")
        self.log(f"  → small delta (large N) → zeros concentrate at 1/2")
        self.log(f"  This would be the 'missing inequality':")
        self.log(f"  |Re(s) - 1/2| <= C * delta(N)^alpha")
        self.check("Spread vs delta measured", True)


if __name__ == "__main__":
    UtoSMap().execute()
