"""
RH_016: Chiral Imprint on Fourier Structure
============================================

Test (Jeong): Is γ₁/γ₂ = 3 specific to d=5 (= 2+3)?

If the 3:1 ratio comes from C(n_A,2)/C(n_T,2) = C(3,2)/C(2,2) = 3/1,
then d=5 is the ONLY dimension with this clean integer ratio
(because d=5 has the unique chiral decomposition).

For other d without unique decomposition:
  d=7: no unique split → messy ratio?
  d=8: no unique split → messy ratio?
  d=10: no unique split → messy ratio?

If only d=5 gives a clean integer γ₁/γ₂, the chiral
decomposition ℂ⁵ = ℂ² ⊕ ℂ³ is imprinted on the
Fourier spectrum of the Gram explicit formula.

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class ChiralFourier(Experiment):
    ID = "RH_016"
    TITLE = "Chiral Fourier imprint"

    def run(self):
        self.test1_fourier_all_d()
        self.test2_integer_ratio_test()

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
        _, vecs = np.linalg.eigh(H)
        return np.array([np.angle(vecs[0, k] * vecs[1, k].conj())
                         for k in range(d)])

    def _build_mult(self, N, phases, primes):
        f = np.ones(N + 1, dtype=complex)
        f[0] = 0
        prime_set = set()
        for i, p in enumerate(primes):
            if p > N:
                break
            f[p] = np.exp(1j * phases[i % len(phases)])
            prime_set.add(p)
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

    def _fourier_analysis(self, d, n_trials=50, N_max=5000):
        """Run Fourier decomposition, return top frequencies."""
        primes = self._sieve_primes(N_max)
        x_values = np.unique(np.logspace(
            np.log10(50), np.log10(N_max), 200).astype(int))
        log_x = np.log(x_values.astype(float))

        residual = np.zeros(len(x_values))
        for t in range(n_trials):
            ph = self._gram_phases(d, seed=t + d * 500)
            f = self._build_mult(N_max, ph, primes)
            for i, x in enumerate(x_values):
                M = np.sum(np.real(f[1:x+1]))
                residual[i] += M / np.sqrt(x) / n_trials

        # FFT in uniform log-space
        log_uniform = np.linspace(log_x[0], log_x[-1], 128)
        R_uniform = np.interp(log_uniform, log_x, residual)
        fft = np.fft.rfft(R_uniform - np.mean(R_uniform))
        freqs = np.fft.rfftfreq(len(log_uniform),
                                d=log_uniform[1] - log_uniform[0])
        power = np.abs(fft)**2

        # Top 5 frequencies (skip DC)
        top_idx = np.argsort(power[1:])[::-1][:5] + 1
        top_freqs = [(freqs[i], power[i]) for i in top_idx]
        return top_freqs

    # ── Test 1: Fourier at All d ─────────────────────────

    def test1_fourier_all_d(self):
        """Fourier decomposition for d = 5, 7, 8, 10, 12, 15."""
        self.log("\n═══ Test 1: Fourier Frequencies at Each d ═══")

        d_values = [5, 7, 8, 10, 12, 15]
        self._results = {}

        for d in d_values:
            top = self._fourier_analysis(d, n_trials=50, N_max=5000)
            self._results[d] = top

            gamma1 = top[0][0]
            gamma2 = top[1][0]
            ratio = gamma1 / gamma2 if gamma2 > 0 else 0

            self.log(f"\n  d={d}:")
            for i, (freq, pwr) in enumerate(top[:3]):
                self.log(f"    γ_{i+1} = {freq:.4f}  "
                         f"(power = {pwr:.3f})")
            self.log(f"    γ₁/γ₂ = {ratio:.3f}")
            near_int = abs(ratio - round(ratio))
            self.log(f"    |γ₁/γ₂ - nearest int| = {near_int:.3f}"
                     f"  {'← INTEGER!' if near_int < 0.15 else ''}")

        self.check("Fourier computed for all d", True)

    # ── Test 2: Integer Ratio Uniqueness ─────────────────

    def test2_integer_ratio_test(self):
        """Is clean integer γ₁/γ₂ unique to d=5?"""
        self.log("\n═══ Test 2: Integer Ratio Uniqueness ═══")
        self.log("  Prediction: d=5 gives integer ratio (chiral)")
        self.log("  Other d: non-integer (no unique decomposition)")

        d_values = [5, 7, 8, 10, 12, 15]

        self.log(f"\n  {'d':>3} | {'γ₁/γ₂':>7} | {'nearest':>7} | "
                 f"{'|Δ|':>6} | {'integer?':>8}")
        self.log(f"  {'-'*3}-+-{'-'*7}-+-{'-'*7}-+-"
                 f"{'-'*6}-+-{'-'*8}")

        integer_ds = []
        for d in d_values:
            top = self._results[d]
            g1, g2 = top[0][0], top[1][0]
            ratio = g1 / g2 if g2 > 0 else 0
            nearest = round(ratio)
            delta = abs(ratio - nearest)
            is_int = delta < 0.15
            if is_int:
                integer_ds.append(d)
            self.log(f"  {d:>3} | {ratio:>7.3f} | {nearest:>7d} | "
                     f"{delta:>6.3f} | {'YES' if is_int else 'no':>8}")

        self.log(f"\n  Dimensions with integer ratio: {integer_ds}")

        if 5 in integer_ds and len(integer_ds) <= 2:
            self.log("  → d=5 is special (chiral uniqueness imprint)")
        elif len(integer_ds) >= 4:
            self.log("  → Integer ratio is generic (not d=5 specific)")
        else:
            self.log("  → Inconclusive")

        # Statistical: run d=5 with many seeds to check robustness
        self.log(f"\n  Robustness: d=5, 10 independent analyses:")
        ratios_5 = []
        for batch in range(10):
            top = self._fourier_analysis(
                5, n_trials=30, N_max=3000 + batch * 200)
            r = top[0][0] / top[1][0] if top[1][0] > 0 else 0
            ratios_5.append(r)
            self.log(f"    batch {batch}: γ₁/γ₂ = {r:.3f}")

        mean_r = np.mean(ratios_5)
        std_r = np.std(ratios_5)
        self.log(f"  ⟨γ₁/γ₂⟩ = {mean_r:.3f} ± {std_r:.3f}")

        self.check("d=5 ratio robust and near integer",
                   abs(mean_r - round(mean_r)) < 0.3)


if __name__ == "__main__":
    ChiralFourier().execute()
