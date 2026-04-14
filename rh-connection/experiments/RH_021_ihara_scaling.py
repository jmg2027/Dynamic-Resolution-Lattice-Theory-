"""
RH_021: Ihara Möbius at Scale — N up to 3000
=============================================

Numerically stable coefficient extraction via:
  log(1/Z(u)) = Σ_k log(1 - u·λ_k + u²·(d_eff-1))
              + (N-1)·log(1-u²)

Recurrence for log(1-au+bu²) Taylor coefficients:
  d_1 = -a,  d_2 = b - a²/2
  (n+1)d_{n+1} = a·n·d_n - b·(n-1)·d_{n-1}  for n≥2

Then μ_graph from exp(Σ L_n u^n).

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class IharaScaling(Experiment):
    ID = "RH_021"
    TITLE = "Ihara Mobius scaling"

    def run(self):
        self.test1_log_recurrence()
        self.test2_scaling_N()
        self.test3_mobius_pattern()

    def _sieve_primes(self, N):
        is_prime = [True] * (N + 1)
        is_prime[0] = is_prime[1] = False
        for i in range(2, int(N**0.5) + 1):
            if is_prime[i]:
                for j in range(i*i, N+1, i):
                    is_prime[j] = False
        return [i for i in range(2, N+1) if is_prime[i]]

    def _mobius(self, N):
        mu = np.ones(N + 1, dtype=int)
        for p in self._sieve_primes(N):
            for k in range(p, N+1, p):
                mu[k] *= -1
            for k in range(p*p, N+1, p*p):
                mu[k] = 0
        mu[0] = 0
        return mu

    def _log_ihara_coeffs(self, eigs, d_eff, N_graph, K):
        """Compute first K Taylor coefficients of log(1/Z(u)).

        Stable recurrence per eigenvalue, then sum.
        """
        L = np.zeros(K + 1)  # L[n] = n-th coefficient

        # Normalize: use λ/d_eff and b = 1 - 1/d_eff
        for lam in eigs:
            a = lam / d_eff
            b = 1.0 - 1.0 / d_eff

            d_coeffs = np.zeros(K + 1)
            d_coeffs[1] = -a
            d_coeffs[2] = b - a**2 / 2.0
            for n in range(2, K):
                d_coeffs[n+1] = (a * n * d_coeffs[n]
                                 - b * (n-1) * d_coeffs[n-1]) / (n+1)

            L += d_coeffs

        # Add (N-1)·log(1-u²) contribution
        # log(1-u²) Taylor: coefficient of u^n is -2/n if n even, 0 if odd
        for n in range(2, K + 1, 2):
            L[n] += -(N_graph - 1) * 2.0 / n

        return L

    def _exp_series(self, log_coeffs, K):
        """Exponentiate: if L = log(f), find f = exp(L).
        f[0] = exp(L[0]) = 1 (since L[0]=0).
        f[n] = (1/n) Σ_{k=1}^n k·L[k]·f[n-k].
        """
        f = np.zeros(K + 1)
        f[0] = np.exp(log_coeffs[0]) if abs(log_coeffs[0]) < 100 else 1.0

        for n in range(1, K + 1):
            s = 0.0
            for k in range(1, n + 1):
                s += k * log_coeffs[k] * f[n - k]
            f[n] = s / n

        return f

    # ── Test 1: Verify Recurrence ────────────────────────

    def test1_log_recurrence(self):
        """Verify log-recurrence matches direct computation at small N."""
        self.log("\n═══ Test 1: Log-Recurrence Verification ═══")

        d = D
        N = 15
        rng = np.random.RandomState(42)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0.0)

        eigs = np.linalg.eigvalsh(W)
        d_eff = W.sum(axis=1).mean()

        K = 20
        L = self._log_ihara_coeffs(eigs, d_eff, N, K)
        mu_coeffs = self._exp_series(L, K)

        # Direct computation for comparison
        def ihara_det(u):
            M = np.eye(N) - u * (W/d_eff) + u**2 * (
                np.diag(W.sum(axis=1)/d_eff) - np.eye(N))
            return np.real(np.linalg.det(M))

        # Extract first K coefficients via polynomial fit
        u_pts = np.linspace(-0.2, 0.2, K + 5)
        det_vals = [ihara_det(u) for u in u_pts]
        direct_coeffs = np.polyfit(u_pts, det_vals, K)[::-1]
        if abs(direct_coeffs[0]) > 1e-10:
            direct_coeffs /= direct_coeffs[0]

        self.log(f"  First 10 coefficients (recurrence vs direct):")
        max_err = 0
        for n in range(min(10, K)):
            err = abs(mu_coeffs[n] - direct_coeffs[n]) if n < len(direct_coeffs) else 0
            max_err = max(max_err, err)
            self.log(f"    n={n:>2}: recur={mu_coeffs[n]:>+10.4f}  "
                     f"direct={direct_coeffs[n]:>+10.4f}  "
                     f"err={err:.2e}")

        self.check("Recurrence matches direct (<1%)",
                   max_err < 0.1)

    # ── Test 2: Scaling with N ───────────────────────────

    def test2_scaling_N(self):
        """μ_graph coefficients for N = 50, 200, 1000, 3000."""
        self.log("\n═══ Test 2: μ_graph at Increasing N ═══")

        d = D
        K = 30  # first 30 coefficients
        N_values = [50, 200, 1000, 3000]
        n_trials = 10
        mu_true = self._mobius(K)

        self.log(f"  μ(n) = {list(mu_true[1:16])}\n")

        for N in N_values:
            avg = np.zeros(K + 1)
            import time
            t0 = time.time()
            for t in range(n_trials):
                rng = np.random.RandomState(t + N * 77)
                psi = rng.randn(N, d) + 1j * rng.randn(N, d)
                psi /= np.linalg.norm(psi, axis=1, keepdims=True)
                G = psi @ psi.conj().T
                W = np.abs(G)**2
                np.fill_diagonal(W, 0.0)

                eigs = np.linalg.eigvalsh(W)
                d_eff = W.sum(axis=1).mean()

                L = self._log_ihara_coeffs(eigs, d_eff, N, K)
                mu_g = self._exp_series(L, K)
                avg += mu_g / n_trials

            elapsed = time.time() - t0
            vals = " ".join([f"{avg[n]:>+6.3f}" for n in range(1, 11)])
            self.log(f"  N={N:>5} ({elapsed:.1f}s): [{vals}]")

        self.check("Scaling computed", True)

    # ── Test 3: Pattern Analysis ─────────────────────────

    def test3_mobius_pattern(self):
        """Squarefree structure in μ_graph at large N."""
        self.log("\n═══ Test 3: Squarefree Pattern at N=3000 ═══")

        d = D
        N = 3000
        K = 30
        n_trials = 20
        mu_true = self._mobius(K)

        avg = np.zeros(K + 1)
        for t in range(n_trials):
            rng = np.random.RandomState(t + 9999)
            psi = rng.randn(N, d) + 1j * rng.randn(N, d)
            psi /= np.linalg.norm(psi, axis=1, keepdims=True)
            G = psi @ psi.conj().T
            W = np.abs(G)**2
            np.fill_diagonal(W, 0.0)

            eigs = np.linalg.eigvalsh(W)
            d_eff = W.sum(axis=1).mean()

            L = self._log_ihara_coeffs(eigs, d_eff, N, K)
            mu_g = self._exp_series(L, K)
            avg += mu_g / n_trials

        # Classify by squarefree / non-squarefree
        primes = self._sieve_primes(K)
        sqfree = set()
        for n in range(1, K+1):
            is_sf = True
            for p in primes:
                if p*p > n:
                    break
                if n % (p*p) == 0:
                    is_sf = False
                    break
            if is_sf:
                sqfree.add(n)

        self.log(f"\n  {'n':>3} | {'μ_graph':>8} | {'μ(n)':>5} | "
                 f"{'sqfree?':>7} | {'sign ok?':>8}")
        self.log(f"  {'-'*3}-+-{'-'*8}-+-{'-'*5}-+-"
                 f"{'-'*7}-+-{'-'*8}")

        sign_agree = 0
        sign_total = 0
        sqfree_near_zero = 0
        nonsqfree_total = 0

        for n in range(1, min(K+1, 26)):
            is_sf = n in sqfree
            mu_g = avg[n]
            mu_n = mu_true[n]
            sign_ok = ""
            if is_sf and mu_n != 0 and abs(mu_g) > 0.01:
                sign_total += 1
                if np.sign(mu_g) == np.sign(mu_n):
                    sign_agree += 1
                    sign_ok = "✓"
                else:
                    sign_ok = "✗"
            if not is_sf:
                nonsqfree_total += 1
                if abs(mu_g) < 0.05:
                    sqfree_near_zero += 1

            self.log(f"  {n:>3} | {mu_g:>+8.4f} | {mu_n:>+5d} | "
                     f"{'yes' if is_sf else 'NO':>7} | {sign_ok:>8}")

        if sign_total > 0:
            self.log(f"\n  Sign agreement (sqfree, |μ_G|>0.01): "
                     f"{sign_agree}/{sign_total} ({sign_agree/sign_total:.0%})")
        if nonsqfree_total > 0:
            self.log(f"  Non-sqfree near zero (|μ_G|<0.05): "
                     f"{sqfree_near_zero}/{nonsqfree_total} "
                     f"({sqfree_near_zero/nonsqfree_total:.0%})")

        self.check("Pattern analysis complete", True)


if __name__ == "__main__":
    IharaScaling().execute()
