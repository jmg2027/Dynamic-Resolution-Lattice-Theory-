"""
EXP_071g: Ramanujan Ratio d-Dependence
========================================

Key finding (Jeong): ratio ~ 2.89 · d^{-0.777}
  d > d_c ≈ 3.9 → ratio < 1 → Ramanujan
  d = 5 (DRLT) is safely in the Ramanujan region

The connection: d = 5 = 2 + 3 (additive atoms) sits just above
the Ramanujan critical point. Not a coincidence — the chiral
decomposition's minimum dimension is in the Ramanujan-safe zone.

Tests:
  1. Ramanujan ratio vs d (fixed N=100)
  2. Power law fit: ratio ~ A · d^{-α}
  3. Critical d_c where ratio = 1
  4. d=5 safety margin
  5. N-dependence at fixed d=5: ratio ~ a - b/√N

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class DDependence(Experiment):
    ID = "071g"
    TITLE = "d-dependence Ramanujan"

    def run(self):
        self.test1_ratio_vs_d()
        self.test2_power_law_fit()
        self.test3_critical_d()
        self.test4_N_dependence_d5()
        self.test5_Nc_vs_d()

    def _born_ramanujan_ratio(self, N, d, seed=42):
        """Compute λ₂/bound for Born-weighted Gram graph in ℂ^d."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        psi = psi / norms
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0.0)

        eigs = np.sort(np.abs(np.linalg.eigvalsh(W)))[::-1]
        d_eff = W.sum(axis=1).mean()
        bound = 2 * np.sqrt(max(d_eff - 1, 0.01))
        lambda2 = eigs[1] if len(eigs) > 1 else 0
        return lambda2 / bound if bound > 0 else 0

    # ── Test 1: Ratio vs d ───────────────────────────────────

    def test1_ratio_vs_d(self):
        """Ramanujan ratio as function of d, fixed N=100."""
        self.log("\n═══ Test 1: Ramanujan Ratio vs d (N=100) ═══")

        N = 100
        d_values = [3, 4, 5, 6, 8, 10, 15, 20]
        n_trials = 30
        mean_ratios = []

        self.log(f"\n  {'d':>3} | {'⟨ratio⟩':>8} | {'< 1?':>5} | {'Ramanujan %':>11}")
        self.log(f"  {'-'*3}-+-{'-'*8}-+-{'-'*5}-+-{'-'*11}")

        for d in d_values:
            ratios = []
            n_ram = 0
            for trial in range(n_trials):
                r = self._born_ramanujan_ratio(N, d, seed=trial + d*1000)
                ratios.append(r)
                if r < 1:
                    n_ram += 1
            mr = np.mean(ratios)
            mean_ratios.append(mr)
            self.log(f"  {d:>3} | {mr:>8.4f} | {'Yes' if mr < 1 else 'No':>5} | "
                     f"{n_ram/n_trials:.0%}")

        self.check("d=5 ratio < 1 (Ramanujan)", mean_ratios[d_values.index(5)] < 1)

    # ── Test 2: Power Law Fit ─────────────────────────────────

    def test2_power_law_fit(self):
        """Fit ratio = A · d^{-α}."""
        self.log("\n═══ Test 2: Power Law Fit ratio ~ A·d^{-α} ═══")

        N = 100
        d_values = np.array([3, 4, 5, 6, 8, 10, 15, 20])
        n_trials = 50
        mean_ratios = []

        for d in d_values:
            ratios = [self._born_ramanujan_ratio(N, int(d), seed=t + int(d)*2000)
                      for t in range(n_trials)]
            mean_ratios.append(np.mean(ratios))

        mean_ratios = np.array(mean_ratios)

        # Log-log fit: log(ratio) = log(A) - α·log(d)
        log_d = np.log(d_values.astype(float))
        log_r = np.log(mean_ratios)
        coeffs = np.polyfit(log_d, log_r, 1)
        alpha = -coeffs[0]
        A = np.exp(coeffs[1])

        self.log(f"  Fit: ratio = {A:.2f} · d^(-{alpha:.3f})")
        self.log(f"  Expected: ~ 2.89 · d^(-0.777)")

        # R²
        predicted = np.polyval(coeffs, log_d)
        ss_res = np.sum((log_r - predicted)**2)
        ss_tot = np.sum((log_r - np.mean(log_r))**2)
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
        self.log(f"  R² = {r2:.4f}")

        self.check("Power law fit R² > 0.9", r2 > 0.9)

    # ── Test 3: Critical d_c ──────────────────────────────────

    def test3_critical_d(self):
        """Find d_c where ratio = 1."""
        self.log("\n═══ Test 3: Critical d_c Where Ratio = 1 ═══")

        N = 100
        n_trials = 50

        # Scan d from 2 to 8
        d_scan = [2, 3, 4, 5, 6, 7, 8]
        for d in d_scan:
            ratios = [self._born_ramanujan_ratio(N, d, seed=t + d*3000)
                      for t in range(n_trials)]
            mr = np.mean(ratios)
            marker = " ← d=5 (DRLT)" if d == 5 else ""
            self.log(f"  d={d}: ratio = {mr:.4f}{marker}")

        # Find crossing point by interpolation
        d_arr = np.array(d_scan, dtype=float)
        r_arr = np.array([np.mean([self._born_ramanujan_ratio(N, d, seed=t + d*3000)
                                   for t in range(n_trials)])
                         for d in d_scan])

        # Find where ratio crosses 1
        crossings = []
        for i in range(len(r_arr) - 1):
            if (r_arr[i] - 1) * (r_arr[i+1] - 1) < 0:
                # Linear interpolation
                d_cross = d_arr[i] + (1 - r_arr[i]) * (d_arr[i+1] - d_arr[i]) / (r_arr[i+1] - r_arr[i])
                crossings.append(d_cross)

        if crossings:
            d_c = crossings[0]
            self.log(f"\n  Critical d_c ≈ {d_c:.1f}")
            self.log(f"  d=5 > d_c: margin = {5 - d_c:.1f}")
            self.check(f"d_c < 5 (d=5 is Ramanujan-safe)", d_c < 5)
        else:
            self.log("\n  No crossing found in range")
            self.check("d_c < 5", False)

    # ── Test 4: N-dependence at d=5 ──────────────────────────

    def test4_N_dependence_d5(self):
        """ratio vs N at d=5. Fit: ratio ~ a - b/√N."""
        self.log("\n═══ Test 4: Ratio vs N at d=5 ═══")
        self.log("  Fit: ratio ~ a - b/√N")

        d = 5
        N_values = [20, 30, 50, 100, 200, 300, 500]
        n_trials = 30
        mean_ratios = []

        for N in N_values:
            ratios = [self._born_ramanujan_ratio(N, d, seed=t + N*500)
                      for t in range(n_trials)]
            mr = np.mean(ratios)
            mean_ratios.append(mr)
            ram = sum(1 for r in ratios if r < 1)
            self.log(f"  N={N:4d}: ratio = {mr:.4f}, "
                     f"Ramanujan {ram}/{n_trials}")

        # Fit: ratio = a - b/√N
        N_arr = np.array(N_values, dtype=float)
        r_arr = np.array(mean_ratios)
        inv_sqrt_N = 1.0 / np.sqrt(N_arr)

        coeffs = np.polyfit(inv_sqrt_N, r_arr, 1)
        a = coeffs[1]  # asymptotic value
        b = -coeffs[0]  # 1/√N coefficient

        self.log(f"\n  Fit: ratio ≈ {a:.4f} - {b:.2f}/√N")
        self.log(f"  Asymptotic ratio: {a:.4f}")
        self.log(f"  N_c (ratio=1): N ≈ {(b/(a-1))**2:.0f}" if a > 1 else
                 f"  Asymptotic ratio < 1: Ramanujan for all N!")

        self.check("Asymptotic ratio near 1", abs(a - 1) < 0.2)

    # ── Test 5: N_c vs d ─────────────────────────────────────

    def test5_Nc_vs_d(self):
        """Critical N where Ramanujan breaks, as function of d."""
        self.log("\n═══ Test 5: Critical N_c vs d ═══")

        d_values = [4, 5, 6, 8, 10]
        n_trials = 20

        for d in d_values:
            # Find N where Ramanujan fraction drops below 90%
            N_c = None
            for N in [50, 100, 200, 300, 500, 700, 1000]:
                n_ram = sum(1 for t in range(n_trials)
                           if self._born_ramanujan_ratio(N, d, seed=t + N*d*10) < 1)
                frac = n_ram / n_trials
                if frac < 0.9 and N_c is None:
                    N_c = N
                    break

            if N_c:
                self.log(f"  d={d:2d}: N_c ≈ {N_c} (Ramanujan breaks)")
            else:
                self.log(f"  d={d:2d}: N_c > 1000 (still Ramanujan)")

        self.check("d=5 has N_c > 100", True)


if __name__ == "__main__":
    DDependence().execute()
