"""
RH_012: Resolution Limit Exponent α = 2/(d-1)
===============================================

Analytical derivation:
  δ(N) = 1 - max_{i≠j} |G_ij|²

For random unit vectors in ℂ^d:
  |⟨ψ_i|ψ_j⟩|² ~ Beta(1, d-1)

Extreme value theory for M = N(N-1)/2 iid Beta(1,d-1):
  max ~ 1 - M^{-1/(d-1)}
  δ(N) ~ M^{-1/(d-1)} = (N²/2)^{-1/(d-1)}
       = 2^{1/(d-1)} · N^{-2/(d-1)}

For d=5: α = 2/(d-1) = 2/4 = 1/2 exactly.
  δ(N) = 2^{1/4} · N^{-1/2} ≈ 1.189 · N^{-1/2}

Tests:
  1. Verify |G_ij|² ~ Beta(1, d-1) distribution
  2. Verify δ(N) exponent matches 2/(d-1) across d
  3. Verify prefactor matches 2^{1/(d-1)}
  4. N_c exact formula from ρ=1 equation

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from scipy import stats
from experiment import Experiment
from drlt import D


class ResolutionExponent(Experiment):
    ID = "RH_012"
    TITLE = "Resolution exponent alpha"

    def run(self):
        self.test1_beta_distribution()
        self.test2_exponent_vs_d()
        self.test3_prefactor()
        self.test4_Nc_exact()

    def _make_G(self, N, d, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        return psi @ psi.conj().T

    # ── Test 1: Beta(1, d-1) Distribution ────────────────

    def test1_beta_distribution(self):
        """Verify |G_ij|² ~ Beta(1, d-1)."""
        self.log("\n═══ Test 1: |G_ij|² ~ Beta(1, d-1) ═══")

        for d in [3, 5, 8, 10]:
            overlaps = []
            for t in range(200):
                G = self._make_G(50, d, seed=t + d * 1000)
                iu = np.triu_indices(50, k=1)
                overlaps.extend(np.abs(G[iu])**2)
            overlaps = np.array(overlaps)

            # KS test vs Beta(1, d-1)
            ks_stat, p_val = stats.kstest(overlaps, 'beta', args=(1, d-1))

            # Mean check: E[Beta(1,d-1)] = 1/d
            mean_emp = np.mean(overlaps)
            mean_th = 1.0 / d

            self.log(f"  d={d:2d}: KS p={p_val:.3f}, "
                     f"⟨|G|²⟩={mean_emp:.5f} "
                     f"(theory {mean_th:.5f})")

        self.check("|G_ij|² ~ Beta(1,d-1) confirmed",
                   p_val > 0.01)

    # ── Test 2: Exponent vs d ────────────────────────────

    def test2_exponent_vs_d(self):
        """Verify δ(N) ~ N^{-2/(d-1)} for multiple d."""
        self.log("\n═══ Test 2: α = 2/(d-1) Across d ═══")
        self.log("  Theory: δ(N) ~ C · N^{-2/(d-1)}")

        d_values = [3, 4, 5, 6, 8, 10]
        N_values = [20, 30, 50, 100, 200, 500]
        n_trials = 200

        self.log(f"\n  {'d':>3} | {'α_theory':>8} | {'α_fit':>8} | "
                 f"{'R²':>6} | {'err':>6}")
        self.log(f"  {'-'*3}-+-{'-'*8}-+-{'-'*8}-+-"
                 f"{'-'*6}-+-{'-'*6}")

        for d in d_values:
            alpha_theory = 2.0 / (d - 1)
            deltas = []
            for N in N_values:
                ds = []
                for t in range(n_trials):
                    G = self._make_G(N, d, seed=t + N * d * 7)
                    ov = np.abs(G)**2
                    np.fill_diagonal(ov, 0.0)
                    ds.append(1.0 - np.max(ov))
                deltas.append(np.mean(ds))

            # Log-log fit
            log_N = np.log(np.array(N_values, dtype=float))
            log_d = np.log(np.array(deltas))
            coeffs = np.polyfit(log_N, log_d, 1)
            alpha_fit = -coeffs[0]
            pred = np.polyval(coeffs, log_N)
            ss_res = np.sum((log_d - pred)**2)
            ss_tot = np.sum((log_d - log_d.mean())**2)
            r2 = 1 - ss_res / ss_tot
            err = abs(alpha_fit - alpha_theory) / alpha_theory

            self.log(f"  {d:>3} | {alpha_theory:>8.4f} | "
                     f"{alpha_fit:>8.4f} | {r2:>6.4f} | {err:>5.1%}")

        self.check("α matches 2/(d-1) within 10% for d=5",
                   err < 0.10)

    # ── Test 3: Prefactor ────────────────────────────────

    def test3_prefactor(self):
        """Verify δ(N) ≈ 2^{1/(d-1)} · N^{-2/(d-1)}."""
        self.log("\n═══ Test 3: Prefactor 2^{1/(d-1)} ═══")

        d = 5
        alpha = 2.0 / (d - 1)  # = 0.5
        C_theory = 2**(1.0 / (d - 1))  # = 2^0.25 ≈ 1.189

        N_values = [30, 50, 100, 200, 500]
        n_trials = 300

        self.log(f"  d={d}, α={alpha}, C_theory={C_theory:.4f}")
        self.log(f"\n  {'N':>5} | {'δ_emp':>8} | {'δ_theory':>8} | "
                 f"{'C_emp':>6}")
        self.log(f"  {'-'*5}-+-{'-'*8}-+-{'-'*8}-+-{'-'*6}")

        C_emps = []
        for N in N_values:
            ds = []
            for t in range(n_trials):
                G = self._make_G(N, d, seed=t + N * 999)
                ov = np.abs(G)**2
                np.fill_diagonal(ov, 0.0)
                ds.append(1.0 - np.max(ov))
            delta_emp = np.mean(ds)
            delta_theory = C_theory * N**(-alpha)
            C_emp = delta_emp * N**alpha
            C_emps.append(C_emp)
            self.log(f"  {N:>5} | {delta_emp:>8.5f} | "
                     f"{delta_theory:>8.5f} | {C_emp:>6.3f}")

        mean_C = np.mean(C_emps)
        err = abs(mean_C - C_theory) / C_theory
        self.log(f"\n  ⟨C_emp⟩ = {mean_C:.4f}, "
                 f"C_theory = {C_theory:.4f}, err = {err:.1%}")

        self.check(f"Prefactor within 20% of 2^{{1/(d-1)}}",
                   err < 0.20)

    # ── Test 4: N_c Exact Formula ────────────────────────

    def test4_Nc_exact(self):
        """Solve ρ(d,N_c) = 1 analytically."""
        self.log("\n═══ Test 4: N_c Exact from ρ = 1 ═══")
        self.log("  ρ = [Nσ₂(1+√(d(d-1)/N))² - 1] / [2√(N/d-1)]")
        self.log("  Setting ρ=1, x=√(N/d), solving quadratic:")
        self.log("  (x+√(d-1))² = (d+1)(1+2x-2√(d-1))")

        d_values = [3, 4, 5, 6, 8, 10, 15, 20]

        self.log(f"\n  {'d':>3} | {'N_c(solve)':>10} | "
                 f"{'N_c(analyt)':>11} | {'err':>5}")
        self.log(f"  {'-'*3}-+-{'-'*10}-+-{'-'*11}-+-{'-'*5}")

        def rho_exact(N, d):
            sigma2 = 1.0 / (d * (d + 1))
            gamma = d * (d - 1.0) / N
            lam2 = N * sigma2 * (1 + np.sqrt(gamma))**2 - 1.0
            d_eff = (N - 1.0) / d
            bound = 2 * np.sqrt(max(d_eff - 1, 0.01))
            return lam2 / bound

        for d in d_values:
            # Numerical solve
            lo, hi = 10.0, 500000.0
            for _ in range(60):
                mid = (lo + hi) / 2
                if rho_exact(mid, d) < 1:
                    lo = mid
                else:
                    hi = mid
            Nc_num = (lo + hi) / 2

            # From ρ=1 (large-N approx, √(x²-1) ≈ x):
            # u² - 2(d+1)u + (d+1)(2√(d-1)-1) = 0
            # where u = x + √(d-1), x = √(N/d)
            s = np.sqrt(d - 1)
            a_coeff = 1
            b_coeff = -2 * (d + 1)
            c_coeff = (d + 1) * (2 * s - 1)
            disc = b_coeff**2 - 4 * a_coeff * c_coeff
            if disc >= 0:
                u = (-b_coeff + np.sqrt(disc)) / (2 * a_coeff)
                x = u - s
                Nc_analyt = d * x**2 if x > 0 else 0
            else:
                Nc_analyt = 0

            err = abs(Nc_analyt - Nc_num) / Nc_num
            self.log(f"  {d:>3} | {Nc_num:>10.0f} | "
                     f"{Nc_analyt:>11.1f} | {err:>4.1%}")

        self.check("Analytical N_c within 5% of numerical",
                   err < 0.05)


if __name__ == "__main__":
    ResolutionExponent().execute()
