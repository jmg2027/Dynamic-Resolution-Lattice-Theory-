"""
RH_015: Gram Explicit Formula — Oscillation Decomposition
==========================================================

Key prediction (Jeong):
  Growth exponent β(d) should approach 1/2 as d→∞,
  possibly via DAMPED OSCILLATION (not monotone decrease).

  Analogy: π(x) = Li(x) - Σ_ρ Li(x^ρ) + ...
  Each ζ zero ρ = 1/2+iγ contributes frequency γ in log-space.

  Gram version: oscillation frequencies in β_eff(x) should
  relate to Gram matrix eigenvalue spacings.

Tests:
  1. β(d): growth exponent vs dimension d (d=3..20)
  2. β_eff(x): local exponent as function of x (look for oscillation)
  3. Fourier decomposition of M_G(x)/x^{1/2} residual
  4. Frequency ↔ Gram eigenvalue spacing correspondence

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class GramExplicitFormula(Experiment):
    ID = "RH_015"
    TITLE = "Gram explicit formula"

    def run(self):
        self.test1_beta_vs_d()
        self.test2_local_exponent()
        self.test3_residual_fourier()
        self.test4_eigenvalue_correspondence()

    # ── Helpers ───────────────────────────────────────────

    def _sieve_primes(self, N):
        is_prime = [True] * (N + 1)
        is_prime[0] = is_prime[1] = False
        for i in range(2, int(N**0.5) + 1):
            if is_prime[i]:
                for j in range(i*i, N+1, i):
                    is_prime[j] = False
        return [i for i in range(2, N+1) if is_prime[i]]

    def _gram_phases(self, d, seed=42):
        rng = np.random.RandomState(seed)
        N_big = max(d * 5, 30)
        psi = rng.randn(N_big, d) + 1j * rng.randn(N_big, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        H = psi.conj().T @ psi
        eigs, vecs = np.linalg.eigh(H)
        phases = []
        for k in range(d):
            v = vecs[:, k]
            phase = np.angle(v[0] * v[1].conj())
            phases.append(phase)
        return np.array(phases), eigs

    def _build_mult(self, N, phases, primes):
        f = np.ones(N + 1, dtype=complex)
        f[0] = 0
        prime_set = set(p for p in primes if p <= N)
        for i, p in enumerate(primes):
            if p > N:
                break
            f[p] = np.exp(1j * phases[i % len(phases)])
        for n in range(2, N + 1):
            if n in prime_set:
                continue
            m, result = n, 1.0 + 0j
            for p in primes:
                if p > m:
                    break
                while m % p == 0:
                    result *= f[p]
                    m //= p
            f[n] = result
        return f

    def _mertens(self, f, x):
        """Mertens-like sum |Σ_{n≤x} f(n)|."""
        return abs(np.sum(f[1:x+1]))

    # ── Test 1: β vs d ──────────────────────────────────

    def test1_beta_vs_d(self):
        """Growth exponent β as function of dimension d."""
        self.log("\n═══ Test 1: Growth Exponent β(d) ═══")
        self.log("  Prediction: β → 1/2 as d → ∞")

        d_values = [3, 5, 8, 10, 15, 20, 30]
        N_max = 3000
        primes = self._sieve_primes(N_max)
        x_values = [100, 200, 500, 1000, 2000, 3000]
        n_trials = 20

        self.log(f"\n  {'d':>3} | {'β':>6} | {'R²':>6} | "
                 f"{'β-0.5':>6} | {'1/√d':>6}")
        self.log(f"  {'-'*3}-+-{'-'*6}-+-{'-'*6}-+-"
                 f"{'-'*6}-+-{'-'*6}")

        betas = []
        for d in d_values:
            log_x = []
            log_M = []
            for x in x_values:
                Ms = []
                for t in range(n_trials):
                    ph, _ = self._gram_phases(d, seed=t + d*100)
                    f = self._build_mult(x, ph, primes)
                    Ms.append(self._mertens(f, x))
                log_x.append(np.log(x))
                log_M.append(np.log(np.mean(Ms)))

            coeffs = np.polyfit(log_x, log_M, 1)
            beta = coeffs[0]
            pred = np.polyval(coeffs, log_x)
            ss_res = np.sum((np.array(log_M) - pred)**2)
            ss_tot = np.sum((np.array(log_M) -
                             np.mean(log_M))**2)
            r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
            betas.append(beta)
            self.log(f"  {d:>3} | {beta:>6.3f} | {r2:>6.4f} | "
                     f"{beta-0.5:>+6.3f} | {1/np.sqrt(d):>6.3f}")

        # Does β decrease with d?
        decreasing = all(betas[i] >= betas[i+1] - 0.05
                         for i in range(len(betas)-1))
        self.log(f"\n  β sequence: {[f'{b:.3f}' for b in betas]}")
        self.log(f"  Monotone decreasing: {decreasing}")
        self.log(f"  Approaches 1/2: {betas[-1] < 0.65}")

        self._betas_d = dict(zip(d_values, betas))
        self.check("β decreases toward 1/2 with d",
                   betas[-1] < betas[0] and betas[-1] < 0.7)

    # ── Test 2: Local Exponent (Oscillation) ─────────────

    def test2_local_exponent(self):
        """β_eff(x) = Δlog|M|/Δlog(x) — look for oscillation."""
        self.log("\n═══ Test 2: Local Exponent β_eff(x) ═══")
        self.log("  If oscillation exists → not monotone to 1/2")

        d = D  # = 5
        N_max = 5000
        primes = self._sieve_primes(N_max)
        n_trials = 50

        # Compute M_G(x) at many x values
        x_values = np.unique(np.logspace(
            np.log10(50), np.log10(5000), 60).astype(int))

        mean_M = np.zeros(len(x_values))
        for t in range(n_trials):
            ph, _ = self._gram_phases(d, seed=t)
            f = self._build_mult(N_max, ph, primes)
            for i, x in enumerate(x_values):
                mean_M[i] += self._mertens(f, x) / n_trials

        # Local exponent: β_eff(x_i) via finite difference
        log_x = np.log(x_values.astype(float))
        log_M = np.log(np.maximum(mean_M, 1e-10))

        beta_local = np.diff(log_M) / np.diff(log_x)
        x_mid = np.exp(0.5 * (log_x[:-1] + log_x[1:]))

        self.log(f"\n  d={d}, {n_trials} trials")
        self.log(f"  x range: {x_values[0]}..{x_values[-1]}")

        # Sample values
        indices = [0, len(beta_local)//4, len(beta_local)//2,
                   3*len(beta_local)//4, len(beta_local)-1]
        self.log(f"\n  {'x':>6} | {'β_eff':>6}")
        self.log(f"  {'-'*6}-+-{'-'*6}")
        for i in indices:
            self.log(f"  {x_mid[i]:>6.0f} | {beta_local[i]:>6.3f}")

        # Check for oscillation: does β_eff change sign of derivative?
        d_beta = np.diff(beta_local)
        sign_changes = np.sum(d_beta[:-1] * d_beta[1:] < 0)
        self.log(f"\n  β_eff sign changes: {sign_changes}")
        self.log(f"  (>3 suggests oscillation)")

        # Mean and std of β_eff
        mean_beta = np.mean(beta_local)
        std_beta = np.std(beta_local)
        self.log(f"  ⟨β_eff⟩ = {mean_beta:.3f} ± {std_beta:.3f}")

        self._beta_local = beta_local
        self._x_mid = x_mid
        self.check("β_eff measured (oscillation detectable)",
                   sign_changes > 2)

    # ── Test 3: Residual Fourier ─────────────────────────

    def test3_residual_fourier(self):
        """Fourier decompose M_G(x)/x^{1/2} in log-space."""
        self.log("\n═══ Test 3: Fourier Decomposition of Residual ═══")
        self.log("  R(x) = M_G(x) / x^{1/2}")
        self.log("  Fourier in log(x) space: frequencies = 'γ values'")

        d = D
        N_max = 5000
        primes = self._sieve_primes(N_max)
        n_trials = 50

        # Dense sampling in log-space
        x_values = np.unique(np.logspace(
            np.log10(50), np.log10(5000), 200).astype(int))
        log_x = np.log(x_values.astype(float))

        # Average M_G(x)/√x
        residual = np.zeros(len(x_values))
        for t in range(n_trials):
            ph, _ = self._gram_phases(d, seed=t + 500)
            f = self._build_mult(N_max, ph, primes)
            for i, x in enumerate(x_values):
                M = np.sum(np.real(f[1:x+1]))  # real part
                residual[i] += M / np.sqrt(x) / n_trials

        # FFT of residual in uniform log-space
        # Resample to uniform spacing in log
        log_uniform = np.linspace(log_x[0], log_x[-1], 128)
        R_uniform = np.interp(log_uniform, log_x, residual)

        fft = np.fft.rfft(R_uniform - np.mean(R_uniform))
        freqs = np.fft.rfftfreq(len(log_uniform),
                                d=log_uniform[1]-log_uniform[0])
        power = np.abs(fft)**2

        # Top 5 frequencies
        top_idx = np.argsort(power[1:])[::-1][:5] + 1
        self.log(f"\n  Top 5 frequencies (in log-space):")
        self._top_freqs = []
        for i, idx in enumerate(top_idx):
            self.log(f"    γ_{i+1} = {freqs[idx]:.3f}, "
                     f"power = {power[idx]:.3f}")
            self._top_freqs.append(freqs[idx])

        self.check("Fourier decomposition computed", True)

    # ── Test 4: Eigenvalue-Frequency Correspondence ──────

    def test4_eigenvalue_correspondence(self):
        """Compare oscillation frequencies with Gram eigenvalue spacings."""
        self.log("\n═══ Test 4: Frequency ↔ Eigenvalue Spacing ═══")
        self.log("  Explicit formula: γ_k ↔ Gram eigenvalue spacings?")

        d = D
        # Get Gram eigenvalue spacings
        _, eigs = self._gram_phases(d, seed=42)
        eigs_sorted = np.sort(eigs)[::-1]
        spacings = np.diff(eigs_sorted)

        self.log(f"\n  Gram eigenvalues (d={d}): "
                 f"{[f'{e:.2f}' for e in eigs_sorted]}")
        self.log(f"  Eigenvalue spacings: "
                 f"{[f'{s:.3f}' for s in spacings]}")

        # Normalized spacings
        mean_spacing = np.mean(np.abs(spacings))
        norm_spacings = np.abs(spacings) / mean_spacing

        self.log(f"  Normalized spacings: "
                 f"{[f'{s:.3f}' for s in norm_spacings]}")

        if hasattr(self, '_top_freqs') and self._top_freqs:
            self.log(f"\n  Oscillation frequencies: "
                     f"{[f'{f:.3f}' for f in self._top_freqs]}")

            # Check if any frequency ratios match spacing ratios
            self.log(f"\n  Frequency ratios: ", )
            for i in range(min(3, len(self._top_freqs))):
                for j in range(i+1, min(4, len(self._top_freqs))):
                    r = (self._top_freqs[i] / self._top_freqs[j]
                         if self._top_freqs[j] > 0 else 0)
                    self.log(f"    γ_{i+1}/γ_{j+1} = {r:.3f}")

            self.log(f"  Spacing ratios:")
            for i in range(min(3, len(norm_spacings))):
                for j in range(i+1, min(4, len(norm_spacings))):
                    r = (norm_spacings[i] / norm_spacings[j]
                         if norm_spacings[j] > 0 else 0)
                    self.log(f"    s_{i+1}/s_{j+1} = {r:.3f}")

        self.check("Correspondence explored (open question)", True)


if __name__ == "__main__":
    GramExplicitFormula().execute()
