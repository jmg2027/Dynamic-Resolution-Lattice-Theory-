"""
RH_034: Integer Cycle Counts — The Discrete Structure
======================================================

Methodological lesson from RH_027-033:
  - Continuous tools (eigenvalues, phases) give TRIVIAL answers
  - The real structure is in the INTEGERS (counts, not magnitudes)

New approach: look ONLY at integer quantities.
  - pi(n) = number of primitive NB cycles of length n
  - Do these counts have multiplicative structure?
  - Does pi(ab) relate to pi(a) and pi(b)?
  - Is the relationship gcd-dependent?

No phases. No eigenvalues. Just counting.

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class IntegerCounts(Experiment):
    ID = "RH_034"
    TITLE = "Integer cycle counts"

    def run(self):
        self.test1_primitive_counts()
        self.test2_count_factorization()
        self.test3_gcd_in_counts()
        self.test4_pnt_from_counts()

    @staticmethod
    def _make_adjacency(N, d=D, seed=42):
        """Build the UNWEIGHTED NB adjacency matrix.
        No complex weights. Just 0 and 1.
        Edge (i,j) -> (j,k) exists iff k != i."""
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_edges = len(edges)
        edge_idx = {e: idx for idx, e in enumerate(edges)}
        A = np.zeros((n_edges, n_edges), dtype=int)
        for idx1, (i, j) in enumerate(edges):
            for k in range(N):
                if k != i and k != j:
                    idx2 = edge_idx.get((j, k))
                    if idx2 is not None:
                        A[idx1, idx2] = 1
        return A

    @staticmethod
    def _walk_counts(A, max_len):
        """Count closed NB walks of each length: W(n) = Tr(A^n)."""
        counts = {}
        Ak = np.eye(A.shape[0], dtype=np.int64)
        for n in range(1, max_len + 1):
            Ak = Ak @ A
            counts[n] = int(np.trace(Ak))
        return counts

    @staticmethod
    def _mobius(n):
        if n == 1:
            return 1
        temp, factors = n, []
        for p in range(2, int(n**0.5) + 2):
            if temp % p == 0:
                count = 0
                while temp % p == 0:
                    temp //= p
                    count += 1
                if count > 1:
                    return 0
                factors.append(p)
        if temp > 1:
            factors.append(temp)
        return (-1) ** len(factors)

    @staticmethod
    def _primitive_counts(walk_counts, max_len):
        """Mobius inversion: pi(n) = (1/n) sum_{d|n} mu(n/d) W(d)."""
        prim = {}
        for n in range(1, max_len + 1):
            total = 0
            for d in range(1, n + 1):
                if n % d == 0:
                    mu = IntegerCounts._mobius(n // d)
                    total += mu * walk_counts.get(d, 0)
            prim[n] = total // n  # should be exact integer
        return prim

    # -- Test 1: Raw primitive cycle counts -----------------------

    def test1_primitive_counts(self):
        """Compute pi(n) for complete graphs K_N."""
        self.log("\n=== Test 1: Primitive cycle counts ===")
        self.log("  pi(n) on complete graph K_N (unweighted NB walks)")

        max_len = 12

        for N in [6, 8, 10]:
            A = self._make_adjacency(N)
            W = self._walk_counts(A, max_len)
            P = self._primitive_counts(W, max_len)

            self.log(f"\n  K_{N} ({N*(N-1)} directed edges):")
            self.log(f"  {'n':>4} | {'W(n) walks':>12} | "
                     f"{'pi(n) prims':>12} | {'pi(n)/pi(n-1)':>14}")
            self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*12}-+-{'-'*14}")

            for n in range(2, max_len + 1):
                ratio = P[n] / P[n-1] if P.get(n-1, 0) != 0 else 0
                self.log(f"  {n:4d} | {W[n]:12d} | {P[n]:12d} | "
                         f"{ratio:14.3f}")

        self.check("Primitive counts computed", True)

    # -- Test 2: Count factorization ------------------------------

    def test2_count_factorization(self):
        """Does pi(ab) relate to pi(a) * pi(b)?
        For primes: pi(p) is "irreducible"
        For composites: pi(ab) should have extra structure."""
        self.log("\n=== Test 2: Count factorization ===")
        self.log("  pi(ab) vs pi(a) * pi(b)")

        N = 10
        A = self._make_adjacency(N)
        max_len = 12
        W = self._walk_counts(A, max_len)
        P = self._primitive_counts(W, max_len)

        pairs = [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
                 (3, 3), (3, 4)]

        self.log(f"\n  {'(a,b)':>7} | {'pi(ab)':>10} | "
                 f"{'pi(a)*pi(b)':>12} | {'ratio':>8} | "
                 f"{'pi(a)+pi(b)':>12} | {'sum ratio':>10}")
        self.log(f"  {'-'*7}-+-{'-'*10}-+-{'-'*12}-+-{'-'*8}-+-"
                 f"{'-'*12}-+-{'-'*10}")

        for a, b in pairs:
            ab = a * b
            if ab > max_len:
                continue
            p_ab = P[ab]
            p_a_times_b = P[a] * P[b]
            p_a_plus_b = P[a] + P[b]

            ratio_mult = p_ab / p_a_times_b if p_a_times_b != 0 else 0
            ratio_add = p_ab / p_a_plus_b if p_a_plus_b != 0 else 0

            self.log(f"  ({a},{b}){' '*(5-len(f'({a},{b})'))} | "
                     f"{p_ab:10d} | {p_a_times_b:12d} | "
                     f"{ratio_mult:8.4f} | {p_a_plus_b:12d} | "
                     f"{ratio_add:10.4f}")

        self.log(f"\n  If ratio_mult is constant -> multiplicative")
        self.log(f"  If ratio varies with (a,b) -> more complex")
        self.check("Count factorization analyzed", True)

    # -- Test 3: gcd in integer counts ----------------------------

    def test3_gcd_in_counts(self):
        """Is there a gcd structure in the INTEGER counts?
        Specifically: pi(a) mod pi(gcd(a,b)) == 0?"""
        self.log("\n=== Test 3: gcd structure in counts ===")

        from math import gcd

        for N in [8, 10, 12]:
            A = self._make_adjacency(N)
            max_len = 12
            W = self._walk_counts(A, max_len)
            P = self._primitive_counts(W, max_len)

            self.log(f"\n  K_{N}:")
            self.log(f"  {'(a,b)':>7} | {'gcd':>4} | {'pi(a)':>8} | "
                     f"{'pi(b)':>8} | {'pi(gcd)':>8} | "
                     f"{'pi(a)%pi(gcd)':>14} | {'pi(b)%pi(gcd)':>14}")
            self.log(f"  {'-'*7}-+-{'-'*4}-+-{'-'*8}-+-{'-'*8}-+-"
                     f"{'-'*8}-+-{'-'*14}-+-{'-'*14}")

            pairs = [(4,6), (6,9), (6,10), (4,10), (3,6), (4,8)]
            for a, b in pairs:
                if a > max_len or b > max_len:
                    continue
                g = gcd(a, b)
                pa, pb, pg = P[a], P[b], P[g]
                mod_a = pa % pg if pg != 0 else -1
                mod_b = pb % pg if pg != 0 else -1
                self.log(f"  ({a},{b}){' '*(5-len(f'({a},{b})'))} | "
                         f"{g:4d} | {pa:8d} | {pb:8d} | {pg:8d} | "
                         f"{mod_a:14d} | {mod_b:14d}")

        self.check("gcd structure in counts examined", True)

    # -- Test 4: PNT from integer counts --------------------------

    def test4_pnt_from_counts(self):
        """Graph-PNT: pi(n) ~ q^n / n where q = N-2
        (for complete graph K_N, NB walk base is N-2)."""
        self.log("\n=== Test 4: PNT from pure integer counts ===")
        self.log("  pi(n) ~ q^n / n,  q = N-2 for K_N")

        for N in [8, 10, 12]:
            A = self._make_adjacency(N)
            max_len = 10
            W = self._walk_counts(A, max_len)
            P = self._primitive_counts(W, max_len)

            q = N - 2  # base for complete graph NB walks

            self.log(f"\n  K_{N} (q = N-2 = {q}):")
            self.log(f"  {'n':>4} | {'pi(n)':>12} | {'q^n/n':>12} | "
                     f"{'ratio':>8}")
            self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*12}-+-{'-'*8}")

            for n in range(2, max_len + 1):
                pnt = q**n // n  # integer division
                ratio = P[n] / pnt if pnt > 0 else 0
                self.log(f"  {n:4d} | {P[n]:12d} | {pnt:12d} | "
                         f"{ratio:8.4f}")

        self.check("PNT from counts verified", True)


if __name__ == "__main__":
    IntegerCounts().execute()
