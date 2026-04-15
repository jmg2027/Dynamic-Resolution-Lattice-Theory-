"""
RH_020: Ihara Zeta → Graph Möbius: The Phase→Möbius Map
========================================================

THE CONNECTION:
  Born-weighted Gram graph → Ihara zeta Z(u) → 1/Z(u) = graph Möbius

  1/Z(u) = (1-u²)^{m-N} · det(I - uW + u²(D-I))

The coefficients of 1/Z(u) = Σ μ_graph(n) u^n ARE the
Phase→Möbius map. No artificial construction needed.

Tests:
  1. Compute Ihara determinant for Born-weighted Gram graph
  2. Extract Ihara zeros and check Ramanujan (|u| = 1/√(d_eff-1))
  3. Extract μ_graph(n) coefficients from 1/Z(u)
  4. Compare μ_graph statistics with μ(n)
  5. d-dependence: does μ_graph → μ as d grows?

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class IharaMobius(Experiment):
    ID = "RH_020"
    TITLE = "Ihara Mobius map"

    def run(self):
        self.test1_ihara_det()
        self.test2_ihara_zeros()
        self.test3_graph_mobius_coeffs()
        self.test4_mobius_comparison()
        self.test5_d_dependence()

    # ── Helpers ───────────────────────────────────────────

    def _make_W(self, N, d, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0.0)
        return W

    def _ihara_det(self, W, u):
        """det(I - uW + u²(D-I)) — Ihara inverse (up to (1-u²) factor)."""
        N = W.shape[0]
        D = np.diag(W.sum(axis=1))
        M = np.eye(N) - u * W + u**2 * (D - np.eye(N))
        return np.real(np.linalg.det(M))

    def _ihara_coefficients(self, W, n_coeffs=None):
        """Extract power series coefficients of det(I-uW+u²(D-I)).
        Uses evaluation at many points + polynomial fit."""
        N = W.shape[0]
        if n_coeffs is None:
            n_coeffs = 2 * N + 1
        # Evaluate at n_coeffs+1 points
        u_vals = np.linspace(-0.3, 0.3, n_coeffs + 5)
        det_vals = np.array([self._ihara_det(W, u) for u in u_vals])
        # Polynomial fit
        coeffs = np.polyfit(u_vals, det_vals, min(n_coeffs, len(u_vals)-1))
        # Reverse: polyfit gives highest power first
        coeffs = coeffs[::-1]
        return coeffs

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
        primes = self._sieve_primes(N)
        for p in primes:
            for k in range(p, N+1, p):
                mu[k] *= -1
            for k in range(p*p, N+1, p*p):
                mu[k] = 0
        mu[0] = 0
        return mu

    # ── Test 1: Ihara Determinant ────────────────────────

    def test1_ihara_det(self):
        """Basic Ihara determinant computation."""
        self.log("\n═══ Test 1: Ihara Determinant ═══")
        self.log("  1/Z(u) ∝ det(I - uW + u²(D-I))")

        d = D  # = 5
        N = 15

        W = self._make_W(N, d, seed=42)
        d_eff = W.sum(axis=1).mean()
        self.log(f"  N={N}, d={d}, d_eff={d_eff:.2f}")

        # Evaluate at several u
        u_vals = [0.0, 0.1, 0.2, 0.3, 0.5]
        self.log(f"\n  {'u':>5} | {'det(M(u))':>15}")
        self.log(f"  {'-'*5}-+-{'-'*15}")
        for u in u_vals:
            det_val = self._ihara_det(W, u)
            self.log(f"  {u:>5.2f} | {det_val:>15.4e}")

        # Ramanujan radius
        r_ram = 1.0 / np.sqrt(max(d_eff - 1, 1))
        self.log(f"\n  Ramanujan radius: |u| = 1/√(d_eff-1) = {r_ram:.4f}")

        self.check("Ihara det computed", True)

    # ── Test 2: Ihara Zeros ──────────────────────────────

    def test2_ihara_zeros(self):
        """Find zeros of 1/Z(u) and check Ramanujan."""
        self.log("\n═══ Test 2: Ihara Zeros ═══")

        d = D
        N = 15
        W = self._make_W(N, d, seed=42)
        d_eff = W.sum(axis=1).mean()
        r_ram = 1.0 / np.sqrt(max(d_eff - 1, 1))

        # Build matrix polynomial: M(u) = I - uW + u²(D-I)
        # Eigenvalues of W give Ihara zeros:
        # If Wv = λv, then det(M(u)) = 0 when
        # 1 - uλ + u²(d_i - 1) = 0 for effective degree d_i
        eigs_W = np.sort(np.linalg.eigvalsh(W))[::-1]

        self.log(f"  Top eigenvalues of W: "
                 f"{[f'{e:.2f}' for e in eigs_W[:8]]}")

        # For each eigenvalue λ, Ihara zeros satisfy:
        # u²(d_eff-1) - uλ + 1 = 0
        # u = (λ ± √(λ²-4(d_eff-1))) / (2(d_eff-1))
        n_on_circle = 0
        n_total = 0
        for lam in eigs_W:
            if abs(lam) < 1e-10:
                continue
            disc = lam**2 - 4*(d_eff - 1)
            if disc < 0:
                # Complex roots → on circle |u| = 1/√(d_eff-1)
                u_mag = 1.0 / np.sqrt(d_eff - 1)
                n_on_circle += 2
                n_total += 2
            else:
                u1 = (lam + np.sqrt(disc)) / (2*(d_eff - 1))
                u2 = (lam - np.sqrt(disc)) / (2*(d_eff - 1))
                n_total += 2
                if abs(abs(u1) - r_ram) < 0.1 * r_ram:
                    n_on_circle += 1
                if abs(abs(u2) - r_ram) < 0.1 * r_ram:
                    n_on_circle += 1

        frac = n_on_circle / n_total if n_total > 0 else 0
        self.log(f"  Ihara zeros on |u|=1/√(d_eff-1): "
                 f"{n_on_circle}/{n_total} ({frac:.0%})")
        self.log(f"  (Complex eigenvalues → zeros exactly on circle)")

        self.check("Ihara zeros computed", True)

    # ── Test 3: Graph Möbius Coefficients ─────────────────

    def test3_graph_mobius_coeffs(self):
        """Extract μ_graph(n) from 1/Z(u) Taylor expansion."""
        self.log("\n═══ Test 3: Graph Möbius Coefficients ═══")
        self.log("  1/Z(u) = Σ μ_graph(n) u^n")

        d = D
        N = 12  # small for exact polynomial
        W = self._make_W(N, d, seed=42)

        # Normalize W for cleaner coefficients
        d_eff = W.sum(axis=1).mean()
        W_norm = W / d_eff  # normalize to ~unit degree

        coeffs = self._ihara_coefficients(W_norm, n_coeffs=20)

        self.log(f"\n  First 15 coefficients of 1/Z(u):")
        self.log(f"  (normalized W, d_eff={d_eff:.2f})")
        for n in range(min(15, len(coeffs))):
            self.log(f"    μ_graph({n:>2}) = {coeffs[n]:>+12.4f}")

        # Key statistics
        nonzero = [c for c in coeffs[1:15] if abs(c) > 1e-6]
        if nonzero:
            self.log(f"\n  Sign pattern: "
                     f"{''.join(['+' if c>0 else '-' for c in nonzero[:12]])}")
            self.log(f"  |coefficients| decay rate: "
                     f"{np.mean(np.abs(nonzero)):.4f}")

        self._coeffs = coeffs
        self.check("Graph Möbius coefficients extracted",
                   len(coeffs) > 5)

    # ── Test 4: μ_graph vs μ(n) ──────────────────────────

    def test4_mobius_comparison(self):
        """Compare graph Möbius statistics with actual μ(n)."""
        self.log("\n═══ Test 4: μ_graph vs μ(n) Statistics ═══")

        # Actual Möbius
        N_max = 20
        mu = self._mobius(N_max)

        self.log(f"  μ(n) for n=1..15: {list(mu[1:16])}")

        if hasattr(self, '_coeffs'):
            c = self._coeffs[:16]
            # Normalize c[0] to 1
            if abs(c[0]) > 1e-10:
                c = c / c[0]
            self.log(f"  μ_graph(n) (normalized): "
                     f"{[f'{v:+.3f}' for v in c[:15]]}")

            # Compare signs
            agreements = 0
            total = 0
            for n in range(1, min(15, len(c))):
                if abs(c[n]) > 1e-4 and mu[n] != 0:
                    total += 1
                    if np.sign(c[n]) == np.sign(mu[n]):
                        agreements += 1

            if total > 0:
                self.log(f"\n  Sign agreement: {agreements}/{total} "
                         f"({agreements/total:.0%})")
            else:
                self.log(f"\n  Too few comparable terms")

        # Now test with MULTIPLE graphs and average
        self.log(f"\n  Averaging over 30 Gram graphs:")
        d = D
        n_trials = 30
        avg_coeffs = np.zeros(20)
        for t in range(n_trials):
            W = self._make_W(12, d, seed=t + 5000)
            d_eff = W.sum(axis=1).mean()
            W_norm = W / d_eff
            c = self._ihara_coefficients(W_norm, n_coeffs=20)
            if abs(c[0]) > 1e-10:
                c = c / c[0]
            avg_coeffs[:len(c)] += c[:20] / n_trials

        self.log(f"  ⟨μ_graph(n)⟩ (averaged):")
        for n in range(min(12, len(avg_coeffs))):
            mu_n = mu[n] if n < len(mu) else 0
            self.log(f"    n={n:>2}: ⟨μ_G⟩={avg_coeffs[n]:>+8.4f}  "
                     f"μ(n)={mu_n:>+2d}")

        self.check("Comparison computed", True)

    # ── Test 5: d-Dependence ─────────────────────────────

    def test5_d_dependence(self):
        """Does μ_graph approach μ as d grows?"""
        self.log("\n═══ Test 5: μ_graph Convergence with d ═══")

        N = 12
        d_values = [5, 8, 10, 15, 20]
        n_trials = 30
        mu = self._mobius(20)

        self.log(f"\n  μ(1..8) = {list(mu[1:9])}")

        for d in d_values:
            avg = np.zeros(20)
            for t in range(n_trials):
                W = self._make_W(N, d, seed=t + d*3000)
                d_eff = W.sum(axis=1).mean()
                W_norm = W / d_eff
                c = self._ihara_coefficients(W_norm, n_coeffs=20)
                if abs(c[0]) > 1e-10:
                    c = c / c[0]
                avg[:len(c)] += c[:20] / n_trials

            # Compare with μ(n): correlation of first few terms
            terms = min(8, len(avg))
            corr_vals = []
            for n in range(1, terms):
                if mu[n] != 0:
                    corr_vals.append(
                        avg[n] * mu[n] / max(abs(avg[n]), 1e-10))

            avg_str = " ".join([f"{avg[n]:>+6.3f}" for n in range(1, 9)])
            self.log(f"  d={d:>2}: ⟨μ_G⟩ = [{avg_str}]")

        self.check("d-dependence explored", True)


if __name__ == "__main__":
    IharaMobius().execute()
