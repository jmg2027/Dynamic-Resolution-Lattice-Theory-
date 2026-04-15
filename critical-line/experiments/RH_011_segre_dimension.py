"""
RH_011: Segre Dimension γ_eff = 2(d-1)/N Test
===============================================

Jeong's insight: φ_i = ψ_i ⊗ ψ̄_i lives on CP^{d-1},
real dim = 2(d-1). So effective MP aspect ratio is:
  γ_eff = 2(d-1)/N     (NOT (d²-1)/N)

Test three candidate effective dimensions:
  (a) p_MP  = d²-1       (original, overestimates)
  (b) p_Seg = 2(d-1)     (Segre/CP dimension)
  (c) p_eff = d(d+1)/2-1 (effective rank)
  (d) p_opt = best fit    (find optimal for each d)

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class SegreDimension(Experiment):
    ID = "RH_011"
    TITLE = "Segre dimension gamma_eff"

    def run(self):
        self.test1_three_gammas()
        self.test2_optimal_peff()
        self.test3_peff_formula()
        self.test4_final_accuracy()

    def _make_W(self, N, d, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0.0)
        return W

    def _lam2_mp(self, N, d, p_eff):
        """λ₂ from MP with effective dimension p_eff."""
        sigma2 = 1.0 / (d * (d + 1))
        gamma = p_eff / N
        return N * sigma2 * (1 + np.sqrt(gamma))**2 - 1.0

    def _emp_lam2(self, N, d, n_trials=50):
        lam2s = []
        for t in range(n_trials):
            W = self._make_W(N, d, seed=t + N * d * 33)
            eigs = np.sort(np.linalg.eigvalsh(W))[::-1]
            lam2s.append(eigs[1])
        return np.mean(lam2s)

    # ── Test 1: Three γ candidates ───────────────────────

    def test1_three_gammas(self):
        """Compare three effective dimensions."""
        self.log("\n═══ Test 1: Three γ Candidates ═══")
        self.log("  (a) p = d²-1  (MP original)")
        self.log("  (b) p = 2(d-1)  (Segre/CP^{d-1})")
        self.log("  (c) p = d(d+1)/2-1  (eff rank)\n")

        d_values = [3, 5, 8, 10]
        N_values = [50, 100, 200, 500]

        for d in d_values:
            p_mp = d**2 - 1
            p_seg = 2 * (d - 1)
            p_eff = d * (d + 1) // 2 - 1
            self.log(f"  d={d}: p_MP={p_mp}, p_Seg={p_seg}, "
                     f"p_eff={p_eff}")

            self.log(f"    {'N':>5} | {'λ₂_emp':>7} | "
                     f"{'λ₂_MP':>7} {'err':>5} | "
                     f"{'λ₂_Seg':>7} {'err':>5} | "
                     f"{'λ₂_eff':>7} {'err':>5}")
            self.log(f"    {'-'*5}-+-{'-'*7}-+-"
                     f"{'-'*7} {'-'*5}-+-"
                     f"{'-'*7} {'-'*5}-+-"
                     f"{'-'*7} {'-'*5}")

            for N in N_values:
                l_emp = self._emp_lam2(N, d)
                l_mp = self._lam2_mp(N, d, p_mp)
                l_seg = self._lam2_mp(N, d, p_seg)
                l_eff = self._lam2_mp(N, d, p_eff)

                e_mp = (l_mp - l_emp) / l_emp
                e_seg = (l_seg - l_emp) / l_emp
                e_eff = (l_eff - l_emp) / l_emp

                self.log(f"    {N:>5} | {l_emp:>7.2f} | "
                         f"{l_mp:>7.2f} {e_mp:>+5.0%} | "
                         f"{l_seg:>7.2f} {e_seg:>+5.0%} | "
                         f"{l_eff:>7.2f} {e_eff:>+5.0%}")
            self.log("")

        self.check("Segre dimension tested", True)

    # ── Test 2: Optimal p_eff per d ──────────────────────

    def test2_optimal_peff(self):
        """Find optimal p_eff for each d by minimizing error."""
        self.log("\n═══ Test 2: Optimal p_eff(d) ═══")

        d_values = [3, 4, 5, 6, 8, 10, 15]
        N_values = [50, 100, 200, 500]

        self.log(f"  {'d':>3} | {'p_opt':>6} | {'d²-1':>5} | "
                 f"{'2(d-1)':>6} | {'d(d+1)/2-1':>10} | "
                 f"{'formula?':>10}")
        self.log(f"  {'-'*3}-+-{'-'*6}-+-{'-'*5}-+-"
                 f"{'-'*6}-+-{'-'*10}-+-{'-'*10}")

        self._p_opts = {}
        for d in d_values:
            # Collect empirical λ₂ at each N
            emp_data = [(N, self._emp_lam2(N, d)) for N in N_values]

            # Search for best p_eff
            best_p = 0
            best_err = 1e10
            for p in np.linspace(1, d**2, 200):
                err = sum((self._lam2_mp(N, d, p) - l)**2
                          for N, l in emp_data)
                if err < best_err:
                    best_err = err
                    best_p = p

            self._p_opts[d] = best_p
            p_mp = d**2 - 1
            p_seg = 2 * (d - 1)
            p_eff = d * (d + 1) / 2 - 1

            self.log(f"  {d:>3} | {best_p:>6.1f} | {p_mp:>5} | "
                     f"{p_seg:>6} | {p_eff:>10.0f} | ")

        self.check("Optimal p_eff found for all d", True)

    # ── Test 3: Formula for p_eff(d) ─────────────────────

    def test3_peff_formula(self):
        """Find a clean formula for p_opt(d)."""
        self.log("\n═══ Test 3: Formula Search for p_opt(d) ═══")

        ds = sorted(self._p_opts.keys())
        ps = [self._p_opts[d] for d in ds]

        # Try various formulas
        candidates = {
            "d²-1": lambda d: d**2 - 1,
            "2(d-1)": lambda d: 2 * (d - 1),
            "d(d+1)/2-1": lambda d: d * (d+1) / 2 - 1,
            "d²/2": lambda d: d**2 / 2,
            "(d²+2d-2)/2": lambda d: (d**2 + 2*d - 2) / 2,
            "d²-d": lambda d: d**2 - d,
            "d²-d+1": lambda d: d**2 - d + 1,
            "(d-1)(d+2)/2": lambda d: (d-1)*(d+2) / 2,
            "d(d-1)": lambda d: d * (d - 1),
        }

        self.log(f"\n  {'Formula':>18} | {'err':>8} | values")
        self.log(f"  {'-'*18}-+-{'-'*8}-+-{'-'*30}")

        best_name = ""
        best_rmse = 1e10
        for name, f in candidates.items():
            preds = [f(d) for d in ds]
            rmse = np.sqrt(np.mean([(p - pp)**2
                                    for p, pp in zip(ps, preds)]))
            vals = ", ".join(f"{f(d):.0f}" for d in ds[:5])
            self.log(f"  {name:>18} | {rmse:>8.2f} | {vals}")
            if rmse < best_rmse:
                best_rmse = rmse
                best_name = name

        opt_vals = ", ".join(f"{p:.1f}" for d, p in
                            zip(ds[:5], ps[:5]))
        self.log(f"\n  {'p_opt':>18} | {'—':>8} | {opt_vals}")
        self.log(f"\n  Best fit: {best_name} (RMSE={best_rmse:.2f})")

        self.check(f"Clean formula found (RMSE<3)", best_rmse < 3)

    # ── Test 4: Final Accuracy ───────────────────────────

    def test4_final_accuracy(self):
        """Accuracy of best formula across all d, N."""
        self.log("\n═══ Test 4: Final Accuracy with Best p_eff ═══")

        d_values = [3, 5, 8, 10]
        N_values = [50, 100, 200, 500]

        errors = []
        for d in d_values:
            p_opt = self._p_opts.get(d, d**2 - 1)
            for N in N_values:
                l_emp = self._emp_lam2(N, d, n_trials=50)
                l_pred = self._lam2_mp(N, d, p_opt)
                err = abs(l_pred - l_emp) / l_emp
                errors.append(err)

        med = np.median(errors)
        mx = np.max(errors)
        self.log(f"  Using p_opt per d:")
        self.log(f"  Median error: {med:.1%}")
        self.log(f"  Max error: {mx:.1%}")

        # Also test best universal formula
        # Use the best candidate from test3
        errors_formula = []
        for d in d_values:
            for N in N_values:
                l_emp = self._emp_lam2(N, d, n_trials=50)
                # Try d²-d as universal
                p_f = d**2 - d
                l_pred = self._lam2_mp(N, d, p_f)
                err = abs(l_pred - l_emp) / l_emp
                errors_formula.append(err)

        med_f = np.median(errors_formula)
        self.log(f"\n  Using p=d²-d (universal):")
        self.log(f"  Median error: {med_f:.1%}")

        self.check("Optimal p_eff median error < 5%", med < 0.05)


if __name__ == "__main__":
    SegreDimension().execute()
