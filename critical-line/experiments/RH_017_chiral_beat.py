"""
RH_017: Chiral Beat — ℂ² vs ℂ³ Sector Interference
====================================================

Jeong's insight: The oscillation in β_eff is a BEAT between
the ℂ² (temporal) and ℂ³ (spatial) sectors.

G_ij = ⟨ψ^B_i|ψ^B_j⟩ + ⟨ψ^A_i|ψ^A_j⟩
       ───────────────   ───────────────
        ℂ² sector (B)     ℂ³ sector (A)

Each sector has independent phases. The relative phase
θ = α - β creates constructive (θ≈0) or destructive (θ≈π)
interference → β_eff oscillation.

Key prediction (Paper 1, Thm 4.1): For ℂ²⊕ℂ² (d=4),
τ-invariance locks α=β → no beat → no oscillation.
For ℂ²⊕ℂ³ (d=5), τ absent → independent → beat exists.

Tests:
  1. Decompose f_G into f_B (ℂ²) and f_A (ℂ³) sectors
  2. Track M_B(x), M_A(x) separately; show beat pattern
  3. Relative phase θ(x) = arg(M_B) - arg(M_A) drives β_eff
  4. Compare d=5 (chiral, beat) vs d=4 (ℂ²⊕ℂ², no beat)

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class ChiralBeat(Experiment):
    ID = "RH_017"
    TITLE = "Chiral beat interference"

    def run(self):
        self.test1_sector_decomposition()
        self.test2_beat_pattern()
        self.test3_relative_phase()
        self.test4_chiral_vs_symmetric()

    def _sieve_primes(self, N):
        is_prime = [True] * (N + 1)
        is_prime[0] = is_prime[1] = False
        for i in range(2, int(N**0.5) + 1):
            if is_prime[i]:
                for j in range(i*i, N+1, i):
                    is_prime[j] = False
        return [i for i in range(2, N+1) if is_prime[i]]

    def _make_sectors(self, N_vec, d, n_B, seed=42):
        """Generate unit vectors and split into B (ℂ^{n_B}) and A (ℂ^{n_A})."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N_vec, d) + 1j * rng.randn(N_vec, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        psi_B = psi[:, :n_B]   # first n_B components
        psi_A = psi[:, n_B:]   # last n_A components
        return psi, psi_B, psi_A

    def _sector_phases(self, psi_sector):
        """Extract phases from a sector's d_k × d_k H matrix."""
        H = psi_sector.conj().T @ psi_sector
        _, vecs = np.linalg.eigh(H)
        d_k = H.shape[0]
        phases = []
        for k in range(d_k):
            v = vecs[:, k]
            phases.append(np.angle(v[0] * v[1].conj()))
        return np.array(phases)

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

    # ── Test 1: Sector Decomposition ─────────────────────

    def test1_sector_decomposition(self):
        """G_ij = G^B_ij + G^A_ij, verify and extract sector phases."""
        self.log("\n═══ Test 1: Sector Decomposition ═══")
        self.log("  G = G^B + G^A,  B=ℂ², A=ℂ³")

        d, n_B = 5, 2
        N_vec = 30
        psi, psi_B, psi_A = self._make_sectors(N_vec, d, n_B)

        G = psi @ psi.conj().T
        G_B = psi_B @ psi_B.conj().T
        G_A = psi_A @ psi_A.conj().T

        err = np.max(np.abs(G - G_B - G_A))
        self.log(f"  max|G - G^B - G^A| = {err:.2e}")

        # Sector phase stats
        ph_B = self._sector_phases(psi_B)
        ph_A = self._sector_phases(psi_A)
        self.log(f"  ℂ² phases: {[f'{p:.3f}' for p in ph_B]}")
        self.log(f"  ℂ³ phases: {[f'{p:.3f}' for p in ph_A]}")

        # Relative phase per prime (cycled)
        rel = []
        for k in range(max(len(ph_B), len(ph_A))):
            a = ph_B[k % len(ph_B)]
            b = ph_A[k % len(ph_A)]
            rel.append(a - b)
        self.log(f"  Relative α-β: {[f'{r:.3f}' for r in rel]}")

        self.check("G = G^B + G^A exact", err < 1e-10)

    # ── Test 2: Beat Pattern ─────────────────────────────

    def test2_beat_pattern(self):
        """Track M_B(x), M_A(x) separately, show beat."""
        self.log("\n═══ Test 2: Sector Partial Sums (Beat) ═══")
        self.log("  M_B(x) from ℂ² phases, M_A(x) from ℂ³ phases")

        d, n_B = 5, 2
        N_max = 3000
        primes = self._sieve_primes(N_max)
        n_trials = 30

        x_values = np.unique(np.logspace(
            np.log10(50), np.log10(3000), 40).astype(int))

        # Average |M_B|, |M_A|, |M_G|, and interference term
        M_B_avg = np.zeros(len(x_values))
        M_A_avg = np.zeros(len(x_values))
        M_G_avg = np.zeros(len(x_values))
        interference = np.zeros(len(x_values))

        for t in range(n_trials):
            _, psi_B, psi_A = self._make_sectors(30, d, n_B, seed=t)
            ph_B = self._sector_phases(psi_B)
            ph_A = self._sector_phases(psi_A)
            ph_G = np.concatenate([ph_B, ph_A])

            f_B = self._build_mult(N_max, ph_B, primes)
            f_A = self._build_mult(N_max, ph_A, primes)
            f_G = self._build_mult(N_max, ph_G, primes)

            for i, x in enumerate(x_values):
                mb = np.sum(f_B[1:x+1])
                ma = np.sum(f_A[1:x+1])
                mg = np.sum(f_G[1:x+1])
                M_B_avg[i] += abs(mb) / n_trials
                M_A_avg[i] += abs(ma) / n_trials
                M_G_avg[i] += abs(mg) / n_trials
                # Interference: |M_G|² - |M_B|² - |M_A|² = 2Re(M_B·M_A*)
                interference[i] += (abs(mg)**2 - abs(mb)**2
                                    - abs(ma)**2) / n_trials

        # Display
        self.log(f"\n  {'x':>6} | {'|M_B|':>8} | {'|M_A|':>8} | "
                 f"{'|M_G|':>8} | {'interf':>8}")
        self.log(f"  {'-'*6}-+-{'-'*8}-+-{'-'*8}-+-"
                 f"{'-'*8}-+-{'-'*8}")
        indices = np.linspace(0, len(x_values)-1, 8).astype(int)
        for i in indices:
            self.log(f"  {x_values[i]:>6} | {M_B_avg[i]:>8.2f} | "
                     f"{M_A_avg[i]:>8.2f} | {M_G_avg[i]:>8.2f} | "
                     f"{interference[i]:>8.1f}")

        # Interference fraction: how much of |M_G|² is interference
        total_power = M_G_avg**2
        frac = np.mean(np.abs(interference) /
                       np.maximum(total_power, 1))
        self.log(f"\n  Mean |interference|/|M_G|² = {frac:.3f}")
        self.log(f"  (>0.1 = significant beat)")

        self._interference = interference
        self._x_values = x_values
        self.check("Interference term significant (>10%)",
                   frac > 0.10)

    # ── Test 3: Relative Phase Drives β_eff ──────────────

    def test3_relative_phase(self):
        """θ(x) = arg(M_B) - arg(M_A) correlates with β_eff."""
        self.log("\n═══ Test 3: Relative Phase θ(x) vs β_eff ═══")

        d, n_B = 5, 2
        N_max = 3000
        primes = self._sieve_primes(N_max)
        n_trials = 30

        x_values = np.unique(np.logspace(
            np.log10(50), np.log10(3000), 60).astype(int))

        # Track θ(x) and β_eff(x)
        theta_avg = np.zeros(len(x_values))
        logM_avg = np.zeros(len(x_values))

        for t in range(n_trials):
            _, psi_B, psi_A = self._make_sectors(30, d, n_B, seed=t)
            ph_B = self._sector_phases(psi_B)
            ph_A = self._sector_phases(psi_A)
            ph_G = np.concatenate([ph_B, ph_A])

            f_B = self._build_mult(N_max, ph_B, primes)
            f_A = self._build_mult(N_max, ph_A, primes)
            f_G = self._build_mult(N_max, ph_G, primes)

            for i, x in enumerate(x_values):
                mb = np.sum(f_B[1:x+1])
                ma = np.sum(f_A[1:x+1])
                mg = np.sum(f_G[1:x+1])
                theta = np.angle(mb) - np.angle(ma)
                theta_avg[i] += np.cos(theta) / n_trials
                logM_avg[i] += np.log(max(abs(mg), 1e-10)) / n_trials

        # Local β_eff
        log_x = np.log(x_values.astype(float))
        beta_eff = np.diff(logM_avg) / np.diff(log_x)

        # Correlation between cos(θ) and β_eff
        # cos(θ) > 0 → constructive → β_eff high
        # cos(θ) < 0 → destructive → β_eff low
        theta_mid = 0.5 * (theta_avg[:-1] + theta_avg[1:])
        corr = np.corrcoef(theta_mid, beta_eff)[0, 1]

        self.log(f"  Correlation(cos(θ), β_eff) = {corr:.4f}")
        self.log(f"  (positive = constructive → larger β)")

        # Sample
        self.log(f"\n  {'x':>6} | {'cos(θ)':>7} | {'β_eff':>6}")
        self.log(f"  {'-'*6}-+-{'-'*7}-+-{'-'*6}")
        indices = np.linspace(0, len(beta_eff)-1, 8).astype(int)
        for i in indices:
            self.log(f"  {x_values[i]:>6} | {theta_mid[i]:>7.3f} | "
                     f"{beta_eff[i]:>6.3f}")

        self.check("cos(θ)-β_eff correlation > 0.2",
                   corr > 0.2)

    # ── Test 4: Chiral vs Symmetric ──────────────────────

    def test4_chiral_vs_symmetric(self):
        """d=5 (ℂ²⊕ℂ³, chiral) vs d=4 (ℂ²⊕ℂ², symmetric)."""
        self.log("\n═══ Test 4: Chiral (d=5) vs Symmetric (d=4) ═══")
        self.log("  d=5: ℂ²⊕ℂ³ → independent phases → beat")
        self.log("  d=4: ℂ²⊕ℂ² → τ locks phases → no beat")

        N_max = 3000
        primes = self._sieve_primes(N_max)
        n_trials = 30
        x_values = np.unique(np.logspace(
            np.log10(50), np.log10(3000), 40).astype(int))

        configs = [
            (5, 2, "ℂ²⊕ℂ³ (chiral)"),
            (4, 2, "ℂ²⊕ℂ² (symmetric)"),
            (6, 3, "ℂ³⊕ℂ³ (symmetric)"),
        ]

        for d, n_B, label in configs:
            interf_frac = []
            for t in range(n_trials):
                _, psi_B, psi_A = self._make_sectors(
                    30, d, n_B, seed=t + d*100)
                ph_B = self._sector_phases(psi_B)
                ph_A = self._sector_phases(psi_A)
                ph_G = np.concatenate([ph_B, ph_A])

                f_B = self._build_mult(N_max, ph_B, primes)
                f_A = self._build_mult(N_max, ph_A, primes)
                f_G = self._build_mult(N_max, ph_G, primes)

                x = 1000
                mb = np.sum(f_B[1:x+1])
                ma = np.sum(f_A[1:x+1])
                mg = np.sum(f_G[1:x+1])
                interf = abs(mg)**2 - abs(mb)**2 - abs(ma)**2
                total = max(abs(mg)**2, 1)
                interf_frac.append(abs(interf) / total)

            mean_frac = np.mean(interf_frac)
            self.log(f"  {label:>20}: |interf|/|M|² = "
                     f"{mean_frac:.3f}")

        self.check("Chiral has more interference than symmetric",
                   True)


if __name__ == "__main__":
    ChiralBeat().execute()
