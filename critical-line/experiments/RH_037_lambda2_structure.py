"""
RH_037: The Second Eigenvalue — Why lambda_2 = 1?
===================================================

RH_036 found: K_N NB adjacency has lambda_1 = N-2, lambda_2 = 1.
Understanding lambda_2 is critical because:
  - It determines the ERROR TERM in graph-PNT
  - Its multiplicity determines how many "error modes" exist
  - Its origin (combinatorial vs algebraic) guides next steps

Tests:
  1. Full spectrum of K_N NB adjacency for N = 6..20
  2. lambda_2 multiplicity vs N
  3. Eigenvalue decomposition: where does lambda = 1 come from?
  4. Compare K_N, cycle graph, Petersen graph

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class Lambda2Structure(Experiment):
    ID = "RH_037"
    TITLE = "Second eigenvalue structure"

    def run(self):
        self.test1_full_spectrum()
        self.test2_multiplicity()
        self.test3_eigenspace()
        self.test4_graph_comparison()

    @staticmethod
    def _nb_adj(N):
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_e = len(edges)
        idx = {e: i for i, e in enumerate(edges)}
        A = np.zeros((n_e, n_e), dtype=int)
        for i1, (a, b) in enumerate(edges):
            for c in range(N):
                if c != a and c != b:
                    i2 = idx.get((b, c))
                    if i2 is not None:
                        A[i1, i2] = 1
        return A

    # -- Test 1: Full spectrum ------------------------------------

    def test1_full_spectrum(self):
        """Complete eigenvalue spectrum of K_N NB adjacency."""
        self.log("\n=== Test 1: Full spectrum ===")

        for N in [6, 8, 10, 12]:
            A = self._nb_adj(N)
            evals = np.linalg.eigvals(A.astype(float))
            evals_real = np.real(evals)
            # Round to identify distinct eigenvalues
            rounded = np.round(evals_real, 4)
            unique, counts = np.unique(rounded, return_counts=True)
            idx_sort = np.argsort(-unique)

            self.log(f"\n  K_{N} ({A.shape[0]} edges):")
            self.log(f"  {'eigenvalue':>12} | {'multiplicity':>12} | note")
            self.log(f"  {'-'*12}-+-{'-'*12}-+-----")

            for i in idx_sort[:8]:
                val = unique[i]
                mult = counts[i]
                note = ""
                if abs(val - (N-2)) < 0.1:
                    note = "lambda_1 = q"
                elif abs(val - 1) < 0.1:
                    note = "lambda_2 = 1"
                elif abs(val + 1) < 0.1:
                    note = "lambda = -1"
                elif abs(val - (-(N-2))) < 0.1:
                    note = "lambda = -q"
                self.log(f"  {val:12.4f} | {mult:12d} | {note}")

        self.check("Full spectrum computed", True)

    # -- Test 2: Multiplicity of lambda_2 = 1 --------------------

    def test2_multiplicity(self):
        """How does the multiplicity of lambda = 1 scale with N?"""
        self.log("\n=== Test 2: Multiplicity of lambda = 1 ===")

        self.log(f"\n  {'N':>4} | {'n_edges':>8} | {'mult(1)':>8} | "
                 f"{'mult(-1)':>8} | {'mult(q)':>8} | {'mult(-q)':>8}")
        self.log(f"  {'-'*4}-+-{'-'*8}-+-{'-'*8}-+-{'-'*8}-+-"
                 f"{'-'*8}-+-{'-'*8}")

        for N in range(4, 16):
            A = self._nb_adj(N)
            evals = np.real(np.linalg.eigvals(A.astype(float)))
            rounded = np.round(evals, 2)

            q = N - 2
            mult_1 = np.sum(np.abs(rounded - 1) < 0.1)
            mult_m1 = np.sum(np.abs(rounded + 1) < 0.1)
            mult_q = np.sum(np.abs(rounded - q) < 0.1)
            mult_mq = np.sum(np.abs(rounded + q) < 0.1)

            self.log(f"  {N:4d} | {A.shape[0]:8d} | {mult_1:8d} | "
                     f"{mult_m1:8d} | {mult_q:8d} | {mult_mq:8d}")

        self.log(f"\n  Look for pattern: mult(1) = f(N)")
        self.check("Multiplicity scaling measured", True)

    # -- Test 3: What IS the lambda=1 eigenspace? -----------------

    def test3_eigenspace(self):
        """Identify the eigenvectors with lambda = 1.
        These tell us WHICH walk patterns contribute to the error."""
        self.log("\n=== Test 3: Eigenspace of lambda = 1 ===")

        N = 8
        A = self._nb_adj(N)
        evals, evecs = np.linalg.eig(A.astype(float))

        # Find lambda ~ 1
        idx_1 = np.where(np.abs(np.real(evals) - 1) < 0.1)[0]
        self.log(f"  K_{N}: {len(idx_1)} eigenvectors with lambda ~ 1")

        edges = [(i, j) for i in range(N) for j in range(N) if i != j]

        if len(idx_1) > 0:
            # Look at first eigenvector with lambda=1
            v = np.real(evecs[:, idx_1[0]])
            # Identify which edges are "active"
            large = np.where(np.abs(v) > 0.1 * np.max(np.abs(v)))[0]

            self.log(f"\n  First eigenvector (lambda=1):")
            self.log(f"  Active edges ({len(large)}/{len(edges)}):")
            for k in large[:10]:
                self.log(f"    edge {edges[k]}: v = {v[k]:.4f}")
            if len(large) > 10:
                self.log(f"    ... ({len(large) - 10} more)")

            # Key question: do these edges form a pattern?
            # Check if it's related to vertex degree
            vertex_sum = np.zeros(N)
            for k, (i, j) in enumerate(edges):
                vertex_sum[i] += v[k]
                vertex_sum[j] += v[k]

            self.log(f"\n  Vertex-projected sum:")
            for i in range(N):
                self.log(f"    vertex {i}: sum = {vertex_sum[i]:.4f}")

        self.check("Eigenspace identified", True)

    # -- Test 4: Compare with other graphs ------------------------

    def test4_graph_comparison(self):
        """Is lambda_2 = 1 specific to K_N or universal?"""
        self.log("\n=== Test 4: lambda_2 for other graphs ===")

        # K_N
        for N in [8, 10]:
            A = self._nb_adj(N)
            evals = np.sort(np.real(np.linalg.eigvals(A.astype(float))))[::-1]
            self.log(f"\n  K_{N}: lam1={evals[0]:.2f}, "
                     f"lam2={evals[1]:.2f}, "
                     f"lam3={evals[2]:.2f}")

        # Cycle graph C_N
        for N in [8, 10]:
            adj = np.zeros((N, N), dtype=int)
            for i in range(N):
                adj[i, (i+1) % N] = 1
                adj[(i+1) % N, i] = 1

            edges = [(i, j) for i in range(N) for j in range(N)
                     if i != j and adj[i, j] > 0]
            n_e = len(edges)
            idx = {e: i for i, e in enumerate(edges)}
            B = np.zeros((n_e, n_e), dtype=int)
            for i1, (a, b) in enumerate(edges):
                for c in range(N):
                    if c != a and adj[b, c] > 0:
                        i2 = idx.get((b, c))
                        if i2 is not None:
                            B[i1, i2] = 1

            evals = np.sort(np.real(np.linalg.eigvals(B.astype(float))))[::-1]
            self.log(f"\n  C_{N} (cycle): lam1={evals[0]:.4f}, "
                     f"lam2={evals[1]:.4f}, "
                     f"lam3={evals[2]:.4f}")

        # Petersen graph
        adj_pet = np.zeros((10, 10), dtype=int)
        petersen_edges = [(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),
                         (3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]
        for i, j in petersen_edges:
            adj_pet[i, j] = adj_pet[j, i] = 1

        edges = [(i, j) for i in range(10) for j in range(10)
                 if i != j and adj_pet[i, j] > 0]
        n_e = len(edges)
        idx = {e: i for i, e in enumerate(edges)}
        B = np.zeros((n_e, n_e), dtype=int)
        for i1, (a, b) in enumerate(edges):
            for c in range(10):
                if c != a and adj_pet[b, c] > 0:
                    i2 = idx.get((b, c))
                    if i2 is not None:
                        B[i1, i2] = 1

        evals = np.sort(np.real(np.linalg.eigvals(B.astype(float))))[::-1]
        self.log(f"\n  Petersen: lam1={evals[0]:.4f}, "
                 f"lam2={evals[1]:.4f}, "
                 f"lam3={evals[2]:.4f}")
        self.log(f"  (Petersen is 3-regular Ramanujan: "
                 f"bound = 2*sqrt(2) = {2*np.sqrt(2):.4f})")

        self.check("Graph comparison done", True)


if __name__ == "__main__":
    Lambda2Structure().execute()
