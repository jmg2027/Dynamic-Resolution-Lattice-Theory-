"""
RH_030: Cycle Factorization — Quantifying Multiplicative Structure
===================================================================

RH_027 Test 3 detected multiplicative phase structure (0.44 vs 1.57).
This experiment quantifies it by examining cycle factorization:

If primitive cycle phases are "primes", do composite cycles factor?
  Phase(ell-cycle) = sum of Phase(primitive factors)?

Tests:
  1. Enumerate primitive cycles for small N
  2. Check factorization: composite cycle phase vs primitive product
  3. Correlation between cycle length and phase clustering
  4. "Euler product" reconstruction from primitives

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class CycleFactorization(Experiment):
    ID = "RH_030"
    TITLE = "Cycle factorization phases"

    def run(self):
        self.test1_trace_factorization()
        self.test2_eigenvalue_phases()
        self.test3_phase_correlations()
        self.test4_euler_reconstruction()

    # -- Helpers (from RH_027) ------------------------------------

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

    # -- Test 1: Trace factorization check ------------------------

    def test1_trace_factorization(self):
        """Check: does Tr(B^{ab}) relate to Tr(B^a) * Tr(B^b)?

        For a multiplicative function f:
          sum_{n=1}^N f(n)/n^s = prod_p (1 + f(p)/p^s + f(p^2)/p^{2s} + ...)

        The trace analog: if cycle phases factorize,
          Tr(B^{ab}) ~ Tr(B^a) * Tr(B^b) (up to corrections)
        """
        self.log("\n=== Test 1: Trace factorization ===")
        self.log("  Check: arg(Tr(B^ab)) vs arg(Tr(B^a)) + arg(Tr(B^b))")

        N = 8
        n_trials = 200
        pairs = [(2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]

        self.log(f"\n  {'(a,b)':>7} | {'mean |diff|':>12} | "
                 f"{'std |diff|':>12} | {'random pi/2':>10} | "
                 f"{'ratio':>6}")
        self.log(f"  {'-'*7}-+-{'-'*12}-+-{'-'*12}-+-{'-'*10}-+-{'-'*6}")

        for a, b in pairs:
            diffs = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                B, _ = self._edge_adjacency(G)

                Ba = np.linalg.matrix_power(B, a)
                Bb = np.linalg.matrix_power(B, b)
                Bab = np.linalg.matrix_power(B, a * b)

                phase_a = np.angle(np.trace(Ba))
                phase_b = np.angle(np.trace(Bb))
                phase_ab = np.angle(np.trace(Bab))

                diff = (phase_ab - phase_a - phase_b + np.pi) % \
                       (2 * np.pi) - np.pi
                diffs.append(abs(diff))

            mean_d = np.mean(diffs)
            std_d = np.std(diffs)
            ratio = mean_d / (np.pi / 2)

            self.log(f"  ({a},{b}){' '*(5-len(f'({a},{b})'))} | "
                     f"{mean_d:12.4f} | {std_d:12.4f} | "
                     f"{np.pi/2:10.4f} | {ratio:6.3f}")

        self.check("Trace factorization analyzed", True)

    # -- Test 2: Eigenvalue phase structure -----------------------

    def test2_eigenvalue_phases(self):
        """The eigenvalues of B encode the primitive cycle structure.

        If lambda_k are eigenvalues of B:
          Tr(B^ell) = sum lambda_k^ell
          Z_G(u)^{-1} = prod (1 - u*lambda_k)

        The PHASE of lambda_k is the "prime phase."
        Are these phases uniform, clustered, or structured?
        """
        self.log("\n=== Test 2: Eigenvalue phases of B ===")

        N = 8
        n_trials = 50
        all_phases = []
        all_mags = []

        for t in range(n_trials):
            G = self._make_gram(N, seed=t)
            B, _ = self._edge_adjacency(G)
            evals = np.linalg.eigvals(B)
            nz = evals[np.abs(evals) > 1e-8]
            all_phases.extend(np.angle(nz))
            all_mags.extend(np.abs(nz))

        all_phases = np.array(all_phases)
        all_mags = np.array(all_mags)

        # Rayleigh test for phase uniformity
        R = abs(np.mean(np.exp(1j * all_phases)))
        self.log(f"  {len(all_phases)} eigenvalues across {n_trials} trials")
        self.log(f"  Rayleigh R = {R:.4f} (0=uniform, 1=concentrated)")

        # Phase histogram
        bins = np.linspace(-np.pi, np.pi, 13)
        counts, _ = np.histogram(all_phases, bins=bins)
        expected = len(all_phases) / 12
        chi2 = np.sum((counts - expected)**2 / expected)
        self.log(f"  Chi-squared uniformity: {chi2:.2f} "
                 f"(critical ~19.7 for 11 df at 5%)")
        self.log(f"  Phases are {'UNIFORM' if chi2 < 19.7 else 'NOT uniform'}")

        # Magnitude distribution
        self.log(f"\n  Magnitude stats: mean={np.mean(all_mags):.3f}, "
                 f"median={np.median(all_mags):.3f}")
        self.log(f"  |lambda| > 1: {np.mean(all_mags > 1):.1%}")
        self.log(f"  |lambda| > 2: {np.mean(all_mags > 2):.1%}")

        self.check("Eigenvalue phases are uniform", chi2 < 19.7)

    # -- Test 3: Phase correlations between lengths ---------------

    def test3_phase_correlations(self):
        """Correlations between arg(Tr(B^a)) and arg(Tr(B^b)).

        If phases are independent: correlation ~ 0.
        If multiplicative: correlation for (a,b) with gcd>1
        should differ from coprime (a,b).
        """
        self.log("\n=== Test 3: Phase correlations ===")

        N = 8
        n_trials = 300
        max_ell = 10

        # Compute phase matrix: phase[t, ell] = arg(Tr(B^ell))
        phases = np.zeros((n_trials, max_ell + 1))
        for t in range(n_trials):
            G = self._make_gram(N, seed=t)
            B, _ = self._edge_adjacency(G)
            Bk = np.eye(B.shape[0], dtype=complex)
            for ell in range(1, max_ell + 1):
                Bk = Bk @ B
                phases[t, ell] = np.angle(np.trace(Bk))

        # Correlation matrix
        self.log(f"\n  Phase correlation matrix (circular):")
        header = "      " + "".join(f" | {b:>5}" for b in range(2, 7))
        self.log(header)
        self.log(f"  {'-'*4}" + "-+------" * 5)

        from math import gcd
        coprime_corrs = []
        noncoprime_corrs = []

        for a in range(2, 7):
            row = f"  {a:4d}"
            for b in range(2, 7):
                # Circular correlation
                diff = phases[:, a] - phases[:, b]
                corr = abs(np.mean(np.exp(1j * diff)))
                if a != b:
                    if gcd(a, b) == 1:
                        coprime_corrs.append(corr)
                    else:
                        noncoprime_corrs.append(corr)
                row += f" | {corr:5.3f}"
            self.log(row)

        mean_coprime = np.mean(coprime_corrs) if coprime_corrs else 0
        mean_noncoprime = np.mean(noncoprime_corrs) if noncoprime_corrs else 0

        self.log(f"\n  Mean corr (coprime pairs):     {mean_coprime:.4f}")
        self.log(f"  Mean corr (non-coprime pairs): {mean_noncoprime:.4f}")
        self.log(f"  Ratio non-coprime/coprime:     "
                 f"{mean_noncoprime/mean_coprime:.3f}"
                 if mean_coprime > 0 else "  N/A")

        # If multiplicative: non-coprime should be MORE correlated
        mult_signal = mean_noncoprime > mean_coprime
        self.log(f"\n  Non-coprime more correlated: "
                 f"{'YES (multiplicative signal)' if mult_signal else 'NO'}")
        self.check("Phase correlations computed", True)

    # -- Test 4: Euler product reconstruction ---------------------

    def test4_euler_reconstruction(self):
        """Try to reconstruct Z_G(u)^{-1} from eigenvalues.

        Z_G(u)^{-1} = prod_k (1 - u*lambda_k)
               = det(I - u*B)

        If we keep only the "large" eigenvalues (primes),
        how much of Z is captured?
        """
        self.log("\n=== Test 4: Euler product reconstruction ===")

        N = 8
        G = self._make_gram(N, seed=42)
        B, _ = self._edge_adjacency(G)
        evals = np.linalg.eigvals(B)

        # Sort by magnitude (largest = most important "primes")
        sorted_evals = evals[np.argsort(-np.abs(evals))]

        # Reconstruct Z^{-1}(u) for u on unit circle
        u_test = 0.9 * np.exp(1j * np.linspace(0, 2*np.pi, 100))

        # Full product
        Z_full = np.array([np.prod(1 - u * evals) for u in u_test])

        # Partial products (top k eigenvalues)
        ks = [5, 10, 20, len(evals)]
        self.log(f"\n  Reconstruction using top-k eigenvalues:")
        self.log(f"  {'k':>5} | {'||Z_k - Z_full|| / ||Z_full||':>30}")
        self.log(f"  {'-'*5}-+-{'-'*30}")

        for k in ks:
            top_k = sorted_evals[:k]
            Z_k = np.array([np.prod(1 - u * top_k) for u in u_test])
            rel_err = np.linalg.norm(Z_k - Z_full) / np.linalg.norm(Z_full)
            self.log(f"  {k:5d} | {rel_err:30.6f}")

        # How many "primes" capture 90% of Z?
        for k in range(1, len(evals)):
            top_k = sorted_evals[:k]
            Z_k = np.array([np.prod(1 - u * top_k) for u in u_test])
            rel_err = np.linalg.norm(Z_k - Z_full) / np.linalg.norm(Z_full)
            if rel_err < 0.1:
                self.log(f"\n  90% accuracy with top {k}/{len(evals)} "
                         f"eigenvalues ({k/len(evals):.0%})")
                break

        self.check("Euler reconstruction computed", True)


if __name__ == "__main__":
    CycleFactorization().execute()
