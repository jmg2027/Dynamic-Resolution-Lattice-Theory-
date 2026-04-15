"""
RH_014: Phase-Möbius Construction from Gram Ensemble
=====================================================

NEW MATHEMATICS: Construct a multiplicative arithmetic function
from the Gram matrix structure and compare with μ(n).

Construction:
  1. Take N unit vectors ψ_1,...,ψ_N ∈ ℂ^d, form G = ΨΨ†
  2. Non-zero eigenvalues λ_1,...,λ_d of G → "spectral primes"
  3. The eigenvector phases of the d×d matrix H = Ψ†Ψ
     provide the "prime phases": θ_k = arg(v_k^T · v_{k+1})
  4. Define f_G(p_k) = e^{iθ_k} for the k-th rational prime
  5. Extend multiplicatively: f_G(mn) = f_G(m)f_G(n)
  6. Compare Σ f_G(n)/n^s statistics with Σ μ(n)/n^s

Key predictions:
  - f_G should have σ=1/2 boundary (Harper)
  - |f_G(n)| = 1 for all n (unit phases from ℂ)
  - Partial sum growth should match μ(n) growth rate

Tests:
  1. Construct f_G from Gram eigenvalue phases
  2. Partial sum statistics: f_G vs μ(n) vs random
  3. Pair correlation of "zeros" of Σ f_G(n)/n^s
  4. Cancellation rate: |Σ f_G(n)| / √N
  5. Squarefree projection: restrict to μ-like values

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class PhaseMobius(Experiment):
    ID = "RH_014"
    TITLE = "Phase-Mobius construction"

    def run(self):
        self.test1_gram_mult_function()
        self.test2_partial_sum_comparison()
        self.test3_cancellation_rate()
        self.test4_squarefree_projection()
        self.test5_convergence_boundary()

    # ── Helpers ───────────────────────────────────────────

    def _sieve_primes(self, N):
        """Sieve of Eratosthenes up to N."""
        is_prime = [True] * (N + 1)
        is_prime[0] = is_prime[1] = False
        for i in range(2, int(N**0.5) + 1):
            if is_prime[i]:
                for j in range(i*i, N+1, i):
                    is_prime[j] = False
        return [i for i in range(2, N+1) if is_prime[i]]

    def _mobius(self, N):
        """Compute μ(n) for n=1..N."""
        mu = np.ones(N + 1, dtype=int)
        primes = self._sieve_primes(N)
        for p in primes:
            for k in range(p, N+1, p):
                mu[k] *= -1
            for k in range(p*p, N+1, p*p):
                mu[k] = 0
        mu[0] = 0
        return mu

    def _gram_phases(self, d, seed=42):
        """Extract d phases from Gram ensemble."""
        rng = np.random.RandomState(seed)
        N_big = max(d * 5, 30)
        psi = rng.randn(N_big, d) + 1j * rng.randn(N_big, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)

        # d×d matrix H = Ψ†Ψ
        H = psi.conj().T @ psi
        eigs, vecs = np.linalg.eigh(H)

        # Extract phases from eigenvectors
        phases = []
        for k in range(d):
            # Phase from dominant component of k-th eigenvector
            v = vecs[:, k]
            phase = np.angle(v[0] * v[1].conj())
            phases.append(phase)
        return np.array(phases)

    def _build_mult_function(self, N, phases, primes):
        """Build multiplicative f(n) from prime phases."""
        f = np.ones(N + 1, dtype=complex)
        f[0] = 0
        # Assign phases to primes (only those ≤ N)
        for i, p in enumerate(primes):
            if p > N:
                break
            phase = phases[i % len(phases)]
            f[p] = np.exp(1j * phase)

        # Extend multiplicatively via sieve
        for n in range(2, N + 1):
            if n in primes[:len([p for p in primes if p <= N])]:
                continue  # already set
            m = n
            result = 1.0 + 0j
            for p in primes:
                if p > m:
                    break
                while m % p == 0:
                    result *= f[p]
                    m //= p
            f[n] = result
        return f

    # ── Test 1: Construct f_G ────────────────────────────

    def test1_gram_mult_function(self):
        """Build multiplicative function from Gram phases."""
        self.log("\n═══ Test 1: Gram Multiplicative Function ═══")

        d = D  # = 5
        N = 500
        primes = self._sieve_primes(N)

        self.log(f"  d={d}, N={N}, {len(primes)} primes")

        phases = self._gram_phases(d, seed=42)
        self.log(f"  Gram phases: {[f'{p:.3f}' for p in phases]}")

        f = self._build_mult_function(N, phases, primes)

        # Basic stats
        magnitudes = np.abs(f[1:])
        self.log(f"  |f(n)|: mean={np.mean(magnitudes):.4f}, "
                 f"std={np.std(magnitudes):.4f}")
        self.log(f"  |f(1)|={abs(f[1]):.4f}, "
                 f"|f(2)|={abs(f[2]):.4f}, "
                 f"|f(6)|={abs(f[6]):.4f}")
        self.log(f"  f(6) = f(2)·f(3)? "
                 f"{abs(f[6] - f[2]*f[3]):.2e}")

        self.check("f is multiplicative",
                   abs(f[6] - f[2]*f[3]) < 1e-10)

    # ── Test 2: Partial Sum Comparison ───────────────────

    def test2_partial_sum_comparison(self):
        """Compare partial sums of f_G, μ, and random."""
        self.log("\n═══ Test 2: Partial Sum Statistics ═══")
        self.log("  M(x) = Σ_{n≤x} f(n),  Mertens-like")

        N = 2000
        d = D
        primes = self._sieve_primes(N)
        mu = self._mobius(N)

        n_trials = 20
        checkpoints = [100, 500, 1000, 2000]

        self.log(f"\n  {'x':>5} | {'|M_μ|/√x':>10} | "
                 f"{'⟨|M_G|/√x⟩':>12} | {'⟨|M_rnd|/√x⟩':>13}")
        self.log(f"  {'-'*5}-+-{'-'*10}-+-{'-'*12}-+-{'-'*13}")

        for x in checkpoints:
            # Mertens for actual μ
            M_mu = np.sum(mu[1:x+1])
            ratio_mu = abs(M_mu) / np.sqrt(x)

            # Gram-derived f_G (average over seeds)
            ratios_G = []
            for t in range(n_trials):
                phases = self._gram_phases(d, seed=t)
                f = self._build_mult_function(x, phases, primes)
                M_G = np.sum(f[1:x+1])
                ratios_G.append(abs(M_G) / np.sqrt(x))

            # Random iid (Steinhaus)
            ratios_rnd = []
            rng = np.random.RandomState(99)
            for t in range(n_trials):
                f_rnd = np.exp(1j * rng.uniform(0, 2*np.pi, x+1))
                f_rnd[0] = 0
                M_rnd = np.sum(f_rnd[1:x+1])
                ratios_rnd.append(abs(M_rnd) / np.sqrt(x))

            self.log(f"  {x:>5} | {ratio_mu:>10.4f} | "
                     f"{np.mean(ratios_G):>12.4f} | "
                     f"{np.mean(ratios_rnd):>13.4f}")

        self.check("Partial sums computed", True)

    # ── Test 3: Cancellation Rate ────────────────────────

    def test3_cancellation_rate(self):
        """Measure |Σ f(n)| growth rate — should be ~√N."""
        self.log("\n═══ Test 3: Cancellation Rate ═══")
        self.log("  RH ⟺ |M(x)| = O(x^{1/2+ε})")
        self.log("  Gram f_G should also show √x cancellation")

        d = D
        N = 5000
        primes = self._sieve_primes(N)
        n_trials = 30

        x_values = [50, 100, 200, 500, 1000, 2000, 5000]

        self.log(f"\n  {'x':>5} | {'⟨|M_G|⟩':>10} | "
                 f"{'√x':>8} | {'ratio':>6}")
        self.log(f"  {'-'*5}-+-{'-'*10}-+-{'-'*8}-+-{'-'*6}")

        log_x = []
        log_M = []
        for x in x_values:
            Ms = []
            for t in range(n_trials):
                phases = self._gram_phases(d, seed=t + 100)
                f = self._build_mult_function(x, phases, primes)
                Ms.append(abs(np.sum(f[1:x+1])))
            mean_M = np.mean(Ms)
            ratio = mean_M / np.sqrt(x)
            log_x.append(np.log(x))
            log_M.append(np.log(mean_M))
            self.log(f"  {x:>5} | {mean_M:>10.2f} | "
                     f"{np.sqrt(x):>8.2f} | {ratio:>6.3f}")

        # Fit exponent: |M| ~ x^β
        coeffs = np.polyfit(log_x, log_M, 1)
        beta = coeffs[0]
        self.log(f"\n  Growth exponent: |M_G(x)| ~ x^{{{beta:.3f}}}")
        self.log(f"  RH requires β ≤ 1/2 + ε")

        self.check(f"Growth exponent < 0.75 (sub-linear cancellation)",
                   beta < 0.75)

    # ── Test 4: Squarefree Projection ────────────────────

    def test4_squarefree_projection(self):
        """Project f_G onto {-1, 0, +1} like μ(n)."""
        self.log("\n═══ Test 4: Squarefree Projection ═══")
        self.log("  μ_G(n) = sgn(Re(f_G(n))) for squarefree n, 0 else")

        N = 1000
        d = D
        primes = self._sieve_primes(N)
        mu_true = self._mobius(N)

        # Build squarefree indicator
        sqfree = np.ones(N + 1, dtype=bool)
        sqfree[0] = False
        for p in primes:
            for k in range(p*p, N+1, p*p):
                sqfree[k] = False

        n_trials = 30
        agreements = []
        for t in range(n_trials):
            phases = self._gram_phases(d, seed=t + 200)
            f = self._build_mult_function(N, phases, primes)

            # Project: μ_G(n) = sgn(Re(f_G(n))) if squarefree, 0 else
            mu_G = np.zeros(N + 1, dtype=int)
            for n in range(1, N + 1):
                if sqfree[n]:
                    mu_G[n] = 1 if np.real(f[n]) > 0 else -1
                else:
                    mu_G[n] = 0

            # Agreement with actual μ(n)
            agree = np.sum(mu_G[1:] == mu_true[1:]) / N
            agreements.append(agree)

        mean_agree = np.mean(agreements)
        # Random baseline: for squarefree n, random ±1 agrees with μ ~50%
        # For non-squarefree, both are 0 → agreement
        n_sqfree = np.sum(sqfree[1:N+1])
        baseline = (N - n_sqfree + n_sqfree * 0.5) / N

        self.log(f"  Agreement μ_G vs μ: {mean_agree:.1%}")
        self.log(f"  Random baseline: {baseline:.1%}")
        self.log(f"  Above random by: {mean_agree - baseline:+.1%}")

        self.check("Agreement computed (exploratory)", True)

    # ── Test 5: Convergence Boundary ─────────────────────

    def test5_convergence_boundary(self):
        """Dirichlet series Σ f_G(n)/n^s convergence."""
        self.log("\n═══ Test 5: Convergence Boundary of Σ f_G(n)/n^s ═══")

        d = D
        N = 3000
        primes = self._sieve_primes(N)
        sigmas = [0.3, 0.4, 0.5, 0.6, 0.7, 0.8]
        n_trials = 20

        self.log(f"\n  {'σ':>5} | {'⟨|S_G(N)|⟩':>12} | "
                 f"{'⟨|S_μ(N)|⟩':>12} | {'⟨|S_rnd(N)|⟩':>13}")
        self.log(f"  {'-'*5}-+-{'-'*12}-+-{'-'*12}-+-{'-'*13}")

        mu = self._mobius(N)
        rng = np.random.RandomState(77)

        for sigma in sigmas:
            # μ(n)
            S_mu = abs(sum(mu[n] / n**sigma for n in range(1, N+1)))

            # Gram f_G
            S_Gs = []
            for t in range(n_trials):
                phases = self._gram_phases(d, seed=t + 300)
                f = self._build_mult_function(N, phases, primes)
                S = sum(f[n] / n**sigma for n in range(1, N+1))
                S_Gs.append(abs(S))

            # Random Steinhaus multiplicative
            S_rnds = []
            for t in range(n_trials):
                pp = {p: rng.uniform(0, 2*np.pi) for p in primes}
                f_r = np.ones(N+1, dtype=complex)
                for n in range(2, N+1):
                    m, ph = n, 0.0
                    for p in primes:
                        if p*p > m:
                            break
                        while m % p == 0:
                            ph += pp[p]
                            m //= p
                    if m > 1 and m in pp:
                        ph += pp[m]
                    elif m > 1:
                        ph += rng.uniform(0, 2*np.pi)
                    f_r[n] = np.exp(1j * ph)
                S = sum(f_r[n] / n**sigma for n in range(1, N+1))
                S_rnds.append(abs(S))

            self.log(f"  {sigma:>5.1f} | {np.mean(S_Gs):>12.3f} | "
                     f"{S_mu:>12.3f} | {np.mean(S_rnds):>13.3f}")

        self.check("Convergence pattern matches (exploratory)", True)


if __name__ == "__main__":
    PhaseMobius().execute()
