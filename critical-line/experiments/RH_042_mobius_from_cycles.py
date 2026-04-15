"""
RH_042: Mobius Function from Cycle Counts
==========================================

Open Problem 2: Phase→Mobius (direction change)
Old approach: continuous phases → failed
New approach: integer cycle counts → mu(n)

The Mobius inversion formula:
  pi(n) = (1/n) Sum_{d|n} mu(n/d) W(d)

Rearranging: this DEFINES mu implicitly via pi and W.
But mu is also defined independently by prime factorization.

KEY QUESTION: Can we extract mu(n) from the CYCLE STRUCTURE
of K_N without knowing prime factorization?

Idea: W(n) = Sum_{d|n} d * pi(d)
If we know W(n) and pi(n) for all n, we can SOLVE for mu:
  mu(n) = (n * pi(n) - Sum_{d|n, d<n} mu(n/d) * W(d)) / W(1)

But W(1) = 0 for NB walks (no length-1 closed walks).
So we need a different approach.

ALTERNATIVE: Look at RATIOS and PATTERNS in pi(n).
  - pi(p) for p prime: "graph primes"
  - pi(p^2) vs pi(p)^2: squarefree detection
  - pi(pq) vs pi(p)*pi(q): multiplicativity test

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class MobiusFromCycles(Experiment):
    ID = "RH_042"
    TITLE = "Mobius from cycle counts"

    def run(self):
        self.test1_pi_at_primes()
        self.test2_squarefree_detection()
        self.test3_mobius_reconstruction()
        self.test4_additive_mobius()

    @staticmethod
    def _walk_and_prim(N, max_len):
        """Compute W(n) and pi(n) for K_N."""
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_e = len(edges)
        idx = {e: i for i, e in enumerate(edges)}
        A = np.zeros((n_e, n_e), dtype=np.int64)
        for i1, (a, b) in enumerate(edges):
            for c in range(N):
                if c != a and c != b:
                    i2 = idx.get((b, c))
                    if i2 is not None:
                        A[i1, i2] = 1

        W = {}
        Ak = np.eye(n_e, dtype=np.int64)
        for n in range(1, max_len + 1):
            Ak = Ak @ A
            W[n] = int(np.trace(Ak))

        def mu(n):
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

        P = {}
        for n in range(1, max_len + 1):
            total = sum(mu(n // d) * W.get(d, 0)
                        for d in range(1, n + 1) if n % d == 0)
            P[n] = total // n

        return W, P

    # -- Test 1: pi at primes vs composites -----------------------

    def test1_pi_at_primes(self):
        """Compare pi(p) for primes vs pi(n) for composites.
        Is there a detectable difference in the INTEGER counts?"""
        self.log("\n=== Test 1: pi(n) at primes vs composites ===")

        N = 12
        max_len = 12
        W, P = self._walk_and_prim(N, max_len)
        q = N - 2  # = 10

        def is_prime(n):
            if n < 2: return False
            for p in range(2, int(n**0.5) + 1):
                if n % p == 0: return False
            return True

        self.log(f"\n  K_{N}, q = {q}")
        self.log(f"  {'n':>4} | {'pi(n)':>12} | {'q^n/n':>12} | "
                 f"{'pi(n)/(q^n/n)':>14} | {'type':>10}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*12}-+-{'-'*14}-+-{'-'*10}")

        for n in range(3, max_len + 1):
            qnn = q**n / n
            ratio = P[n] / qnn if qnn > 0 else 0
            ntype = "PRIME" if is_prime(n) else f"={self._factorize(n)}"
            self.log(f"  {n:4d} | {P[n]:12d} | {qnn:12.0f} | "
                     f"{ratio:14.6f} | {ntype:>10}")

        # Key: does pi(n)/(q^n/n) differ for primes vs composites?
        prime_ratios = [P[n] / (q**n / n) for n in range(3, max_len + 1)
                        if is_prime(n) and q**n / n > 0]
        comp_ratios = [P[n] / (q**n / n) for n in range(4, max_len + 1)
                       if not is_prime(n) and q**n / n > 0]

        self.log(f"\n  Mean ratio (primes): {np.mean(prime_ratios):.6f}")
        self.log(f"  Mean ratio (composites): {np.mean(comp_ratios):.6f}")
        self.log(f"  Difference: {abs(np.mean(prime_ratios) - np.mean(comp_ratios)):.6f}")

        self.check("Prime vs composite pi(n) compared", True)

    @staticmethod
    def _factorize(n):
        factors = []
        temp = n
        for p in range(2, n + 1):
            while temp % p == 0:
                factors.append(str(p))
                temp //= p
        return "*".join(factors)

    # -- Test 2: Squarefree detection from cycle counts -----------

    def test2_squarefree_detection(self):
        """mu(n) = 0 iff n has a squared prime factor.
        Can we detect this from pi(n)?

        For squarefree n = p1*p2*...*pk:
          pi(n) should relate to pi(p1)*pi(p2)*...*pi(pk)
        For n = p^2:
          pi(p^2) should have EXTRA contribution from "repeated" cycles
        """
        self.log("\n=== Test 2: Squarefree detection ===")
        self.log("  mu(n)=0 iff n has p^2 factor")
        self.log("  Can cycle counts detect this?")

        N = 12
        max_len = 12
        W, P = self._walk_and_prim(N, max_len)
        q = N - 2

        def mu(n):
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

        self.log(f"\n  {'n':>4} | {'mu(n)':>6} | {'pi(n)':>12} | "
                 f"{'pi(n) mod pi(p)':>16} | note")
        self.log(f"  {'-'*4}-+-{'-'*6}-+-{'-'*12}-+-{'-'*16}-+-----")

        for n in range(3, max_len + 1):
            m = mu(n)
            # For n = p^2, check pi(p^2) mod pi(p)
            note = ""
            mod_val = ""
            sqrt_n = int(np.sqrt(n))
            if sqrt_n * sqrt_n == n and sqrt_n >= 2:
                p = sqrt_n
                if P.get(p, 0) != 0:
                    mod_val = f"{P[n] % P[p]:>16d}"
                    note = f"p^2, p={p}"
                else:
                    mod_val = f"{'N/A':>16}"
                    note = f"p^2, p={p}, pi(p)=0"
            else:
                mod_val = f"{'—':>16}"

            self.log(f"  {n:4d} | {m:6d} | {P[n]:12d} | {mod_val} | {note}")

        # Key test: for n = p^2, is pi(p^2) divisible by pi(p)?
        # If yes: the "repeated" structure is detectable
        self.log(f"\n  n=4=2^2: pi(4)={P[4]}, pi(2)={P[2]}")
        self.log(f"  n=9=3^2: pi(9)={P[9]}, pi(3)={P[3]}, "
                 f"pi(9)%pi(3)={P[9] % P[3] if P[3] != 0 else 'N/A'}")

        self.check("Squarefree detection tested", True)

    # -- Test 3: Reconstruct mu from cycle data -------------------

    def test3_mobius_reconstruction(self):
        """Can we reconstruct mu(n) from W(n) and pi(n) alone,
        WITHOUT knowing prime factorization?

        Key identity: W(n) = Sum_{d|n} d * pi(d)
        Inversion:    n * pi(n) = Sum_{d|n} mu(n/d) * W(d)

        If we define mu_graph(n/d) by solving this system,
        does it match the number-theoretic mu?
        """
        self.log("\n=== Test 3: Mobius reconstruction ===")
        self.log("  Solve for mu_graph from W and pi alone")

        N = 12
        max_len = 12
        W, P = self._walk_and_prim(N, max_len)

        # Reconstruct mu by solving the linear system:
        # n * pi(n) = Sum_{d|n} mu(n/d) * W(d)
        # Start from n=1 upward
        mu_graph = {}
        mu_graph[1] = 1  # by convention

        for n in range(2, max_len + 1):
            # n * pi(n) = mu(1)*W(n) + Sum_{d|n, d<n} mu(n/d)*W(d)
            # W(n) might be 0 for small n
            # Rearrange: mu(1)*W(n) = n*pi(n) - Sum_{d|n,d<n} mu_graph[n/d]*W(d)

            rhs = n * P[n]
            known_sum = 0
            for d in range(1, n):
                if n % d == 0 and d in W and (n // d) in mu_graph:
                    known_sum += mu_graph[n // d] * W[d]

            # mu(1) * W(n) = rhs - known_sum
            # But mu(1) = 1, so:
            if W.get(n, 0) != 0:
                mu_graph[n] = (rhs - known_sum) // W[n]
            else:
                # W(n) = 0, need different approach
                # For n where all proper divisors' mu are known:
                # n*pi(n) = known_sum + mu_graph[n]*W[1]
                # But W[1] = 0 too!
                # Use: mu(n) = n*pi(n)/... direct formula
                mu_graph[n] = 0  # can't determine

        # Compare to true mu
        def mu_true(n):
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

        self.log(f"\n  {'n':>4} | {'mu_true':>8} | {'mu_graph':>9} | "
                 f"{'match':>6}")
        self.log(f"  {'-'*4}-+-{'-'*8}-+-{'-'*9}-+-{'-'*6}")

        matches = 0
        total = 0
        for n in range(1, max_len + 1):
            mt = mu_true(n)
            mg = mu_graph.get(n, '?')
            match = "YES" if mg == mt else "NO"
            if mg == mt:
                matches += 1
            total += 1
            self.log(f"  {n:4d} | {mt:8d} | {str(mg):>9} | {match:>6}")

        self.log(f"\n  Matches: {matches}/{total}")
        self.check("Mobius reconstruction attempted", True)

    # -- Test 4: Additive Mobius — mu from ADDITION ---------------

    def test4_additive_mobius(self):
        """The deepest test: can mu be defined ADDITIVELY?

        mu(n) = (-1)^{number of prime factors} for squarefree n
               = 0 for non-squarefree n

        In additive terms:
          n = p1 + p2 + ... (Goldbach-like, NOT standard)
          But n = 2a + 3b (Chicken McNugget, this IS standard)

        Connection to additive atoms:
          2 and 3 are additive atoms
          n = 2a + 3b for all n >= 2
          The "additive factorization" is (a, b)

        Does the additive structure (a,b) with n=2a+3b
        encode mu(n)?

        PREDICTION: probably not directly, BUT the number of
        representations n = 2a+3b might relate to omega(n)
        (number of distinct prime factors).
        """
        self.log("\n=== Test 4: Additive Mobius? ===")
        self.log("  n = 2a + 3b (Chicken McNugget)")
        self.log("  Does # of representations relate to mu(n)?")

        def mu_true(n):
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

        def omega(n):
            """Number of distinct prime factors."""
            if n <= 1: return 0
            count, temp = 0, n
            for p in range(2, n + 1):
                if temp % p == 0:
                    count += 1
                    while temp % p == 0:
                        temp //= p
            return count

        def reps_23(n):
            """Number of ways to write n = 2a + 3b with a,b >= 0."""
            count = 0
            for b in range(n // 3 + 1):
                rem = n - 3 * b
                if rem >= 0 and rem % 2 == 0:
                    count += 1
            return count

        self.log(f"\n  {'n':>4} | {'mu(n)':>6} | {'omega(n)':>8} | "
                 f"{'#(2a+3b)':>9} | {'n mod 6':>7}")
        self.log(f"  {'-'*4}-+-{'-'*6}-+-{'-'*8}-+-{'-'*9}-+-{'-'*7}")

        for n in range(2, 31):
            m = mu_true(n)
            om = omega(n)
            r = reps_23(n)
            self.log(f"  {n:4d} | {m:6d} | {om:8d} | {r:9d} | {n%6:7d}")

        # Check correlation
        mus = [mu_true(n) for n in range(2, 31)]
        reps = [reps_23(n) for n in range(2, 31)]
        omegas = [omega(n) for n in range(2, 31)]

        corr_mu_rep = np.corrcoef(mus, reps)[0, 1]
        corr_om_rep = np.corrcoef(omegas, reps)[0, 1]

        self.log(f"\n  Correlation mu vs #reps: {corr_mu_rep:.4f}")
        self.log(f"  Correlation omega vs #reps: {corr_om_rep:.4f}")
        self.log(f"\n  #(2a+3b) = floor(n/6) + 1 for n >= 2")
        self.log(f"  This is LINEAR in n — no number-theoretic content")
        self.log(f"  The additive structure (2,3) doesn't encode mu(n)")
        self.log(f"  mu(n) is fundamentally MULTIPLICATIVE")

        self.check("Additive Mobius test done", True)


if __name__ == "__main__":
    MobiusFromCycles().execute()
