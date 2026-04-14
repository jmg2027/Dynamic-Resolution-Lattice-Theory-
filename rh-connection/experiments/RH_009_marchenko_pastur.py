"""
RH_009: Marchenko-Pastur Prediction for Born-Ramanujan Ratio
=============================================================

Key theoretical result:
  W = Φ†Φ - I,  where φ_i = ψ_i ⊗ ψ̄_i ∈ ℂ^{d²}

Population covariance E[φφ†] has eigenvalues:
  σ₁ = 1/d         (multiplicity 1, vec(I) direction)
  σ₂ = 1/(d(d+1))  (multiplicity d²-1, traceless directions)

Marchenko-Pastur upper edge for bulk cluster:
  λ₂(W) ≈ N·σ₂·(1 + √γ)² - 1,  γ = (d²-1)/N

This gives a CLOSED-FORM formula for ρ(d,N) and N_c(d).

Tests:
  1. Verify Khatri-Rao decomposition: W+I = Φ†Φ
  2. Verify population eigenvalues of E[φφ†]
  3. Compare MP prediction λ₂ vs measured λ₂
  4. Compare MP-predicted ρ(d,N) vs measured ρ
  5. Derive N_c(d) from MP formula

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class MarchenkoPastur(Experiment):
    ID = "RH_009"
    TITLE = "Marchenko-Pastur Born-Ramanujan"

    def run(self):
        self.test1_khatri_rao()
        self.test2_population_cov()
        self.test3_lambda2_prediction()
        self.test4_rho_prediction()
        self.test5_Nc_formula()

    # ── Helpers ───────────────────────────────────────────

    def _make_psi(self, N, d, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        return psi / norms

    def _make_W(self, N, d, seed=42):
        psi = self._make_psi(N, d, seed)
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0.0)
        return W

    def _mp_lambda2(self, N, d):
        """Marchenko-Pastur prediction for λ₂(W)."""
        sigma2 = 1.0 / (d * (d + 1))
        gamma = (d**2 - 1.0) / N
        return N * sigma2 * (1 + np.sqrt(gamma))**2 - 1.0

    def _mp_rho(self, N, d):
        """MP-predicted Ramanujan ratio."""
        lam2 = self._mp_lambda2(N, d)
        d_eff = (N - 1.0) / d
        bound = 2 * np.sqrt(max(d_eff - 1, 0.01))
        return lam2 / bound if bound > 0 else 0

    # ── Test 1: Khatri-Rao Decomposition ─────────────────

    def test1_khatri_rao(self):
        """Verify W + I = Φ†Φ where φ_i = ψ_i ⊗ ψ̄_i."""
        self.log("\n═══ Test 1: Khatri-Rao Decomposition ═══")
        self.log("  W + I = Φ†Φ,  φ_i = ψ_i ⊗ conj(ψ_i)")

        d = 5
        N = 30
        psi = self._make_psi(N, d, seed=42)

        # Build W directly
        G = psi @ psi.conj().T
        W_direct = np.abs(G)**2

        # Build via Khatri-Rao
        Phi = np.zeros((N, d**2), dtype=complex)
        for i in range(N):
            Phi[i] = np.kron(psi[i], psi[i].conj())

        W_kr = Phi @ Phi.conj().T  # This should be W + I

        err = np.max(np.abs(W_direct - W_kr.real))
        self.log(f"  max|W_direct - Φ†Φ| = {err:.2e}")
        self.check("Khatri-Rao identity W+I = Φ†Φ", err < 1e-10)

    # ── Test 2: Population Covariance ────────────────────

    def test2_population_cov(self):
        """Verify E[φφ†] eigenvalues: 1/d and 1/(d(d+1))."""
        self.log("\n═══ Test 2: Population Covariance E[φφ†] ═══")
        self.log("  Theory: σ₁=1/d (×1), σ₂=1/(d(d+1)) (×d²-1)")

        for d in [3, 5, 8, 10]:
            N = 10000  # large sample for convergence
            psi = self._make_psi(N, d, seed=77)
            Phi = np.zeros((N, d**2), dtype=complex)
            for i in range(N):
                Phi[i] = np.kron(psi[i], psi[i].conj())

            # Sample covariance
            Sigma_hat = Phi.conj().T @ Phi / N
            eigs = np.sort(np.linalg.eigvalsh(Sigma_hat))[::-1]

            sigma1_theory = 1.0 / d
            sigma2_theory = 1.0 / (d * (d + 1))

            sigma1_emp = eigs[0]
            sigma2_emp = np.mean(eigs[1:d**2])

            err1 = abs(sigma1_emp - sigma1_theory) / sigma1_theory
            err2 = abs(sigma2_emp - sigma2_theory) / sigma2_theory

            self.log(f"  d={d:2d}: σ₁={sigma1_emp:.5f} "
                     f"(theory {sigma1_theory:.5f}, err {err1:.1%})")
            self.log(f"        σ₂={sigma2_emp:.5f} "
                     f"(theory {sigma2_theory:.5f}, err {err2:.1%})")

        self.check("Population eigenvalues match (<2%)",
                   err1 < 0.02 and err2 < 0.02)

    # ── Test 3: λ₂ Prediction ───────────────────────────

    def test3_lambda2_prediction(self):
        """Compare MP-predicted λ₂ vs measured."""
        self.log("\n═══ Test 3: λ₂(W) — MP Prediction vs Measured ═══")
        self.log("  λ₂_MP = N·σ₂·(1+√γ)² - 1")
        self.log("  σ₂ = 1/(d(d+1)),  γ = (d²-1)/N")

        d = 5
        N_values = [30, 50, 100, 200, 500]
        n_trials = 50

        self.log(f"\n  {'N':>5} | {'λ₂_MP':>8} | {'λ₂_emp':>8} | "
                 f"{'ratio':>6} | {'rel err':>8}")
        self.log(f"  {'-'*5}-+-{'-'*8}-+-{'-'*8}-+-"
                 f"{'-'*6}-+-{'-'*8}")

        max_err = 0
        for N in N_values:
            lam2_mp = self._mp_lambda2(N, d)
            lam2s = []
            for t in range(n_trials):
                W = self._make_W(N, d, seed=t + N * 100)
                eigs = np.sort(np.linalg.eigvalsh(W))[::-1]
                lam2s.append(eigs[1])
            lam2_emp = np.mean(lam2s)
            ratio = lam2_emp / lam2_mp if lam2_mp != 0 else 0
            err = abs(ratio - 1)
            max_err = max(max_err, err)
            self.log(f"  {N:>5} | {lam2_mp:>8.3f} | {lam2_emp:>8.3f} | "
                     f"{ratio:>6.3f} | {err:>7.1%}")

        self.check("λ₂ MP prediction within 25% for all N",
                   max_err < 0.25)

    # ── Test 4: ρ(d,N) Prediction ────────────────────────

    def test4_rho_prediction(self):
        """Compare MP-predicted ρ vs measured across d and N."""
        self.log("\n═══ Test 4: ρ(d,N) — MP Prediction vs Measured ═══")

        d_values = [3, 5, 8, 10]
        N_values = [50, 100, 200, 500]
        n_trials = 30

        self.log(f"\n  {'d':>3} {'N':>5} | {'ρ_MP':>7} | "
                 f"{'ρ_emp':>7} | {'ratio':>6}")
        self.log(f"  {'-'*3} {'-'*5}-+-{'-'*7}-+-"
                 f"{'-'*7}-+-{'-'*6}")

        errors = []
        for d in d_values:
            for N in N_values:
                rho_mp = self._mp_rho(N, d)
                rhos = []
                for t in range(n_trials):
                    W = self._make_W(N, d, seed=t + N * d * 50)
                    eigs = np.sort(np.linalg.eigvalsh(W))[::-1]
                    d_eff = W.sum(axis=1).mean()
                    bound = 2 * np.sqrt(max(d_eff - 1, 0.01))
                    rhos.append(eigs[1] / bound)
                rho_emp = np.mean(rhos)
                ratio = rho_emp / rho_mp if rho_mp != 0 else 0
                errors.append(abs(ratio - 1))
                self.log(f"  {d:>3} {N:>5} | {rho_mp:>7.4f} | "
                         f"{rho_emp:>7.4f} | {ratio:>6.3f}")

        median_err = np.median(errors)
        self.log(f"\n  Median |ratio-1| = {median_err:.1%}")
        self.check("Median ρ error < 20%", median_err < 0.20)

    # ── Test 5: N_c(d) Formula ───────────────────────────

    def test5_Nc_formula(self):
        """Derive N_c(d) where ρ_MP = 1."""
        self.log("\n═══ Test 5: Critical N_c(d) from MP Formula ═══")
        self.log("  Solve: N·σ₂·(1+√γ)² - 1 = 2√(N/d - 1)")
        self.log("  σ₂ = 1/(d(d+1)),  γ = (d²-1)/N")

        d_values = [3, 4, 5, 6, 8, 10, 15, 20]

        self.log(f"\n  {'d':>3} | {'N_c(MP)':>8} | {'ρ_iid':>7} | "
                 f"{'ρ_∞ ~ √(dN)/(2(d+1))':>22}")
        self.log(f"  {'-'*3}-+-{'-'*8}-+-{'-'*7}-+-{'-'*22}")

        for d in d_values:
            # Binary search for N_c where ρ_MP = 1
            lo, hi = 10, 100000
            for _ in range(50):
                mid = (lo + hi) / 2
                if self._mp_rho(mid, d) < 1:
                    lo = mid
                else:
                    hi = mid
            Nc = int((lo + hi) / 2)

            rho_iid = np.sqrt((d - 1) / (d * (d + 1)))
            # Asymptotic: ρ ~ √(dN)/(2(d+1)) for large N
            rho_asymp_formula = f"√({d}N)/{2*(d+1)}"

            self.log(f"  {d:>3} | {Nc:>8d} | {rho_iid:>7.4f} | "
                     f"{rho_asymp_formula:>22}")

        # Fit N_c ~ C·d^δ
        Ncs = []
        ds = np.array([3, 4, 5, 6, 8, 10, 15, 20], dtype=float)
        for d in ds:
            lo, hi = 10.0, 100000.0
            for _ in range(50):
                mid = (lo + hi) / 2
                if self._mp_rho(mid, int(d)) < 1:
                    lo = mid
                else:
                    hi = mid
            Ncs.append((lo + hi) / 2)
        Ncs = np.array(Ncs)

        log_d = np.log(ds)
        log_Nc = np.log(Ncs)
        coeffs = np.polyfit(log_d, log_Nc, 1)
        delta = coeffs[0]
        C = np.exp(coeffs[1])

        pred = np.polyval(coeffs, log_d)
        ss_res = np.sum((log_Nc - pred)**2)
        ss_tot = np.sum((log_Nc - log_Nc.mean())**2)
        r2 = 1 - ss_res / ss_tot

        self.log(f"\n  Fit: N_c ≈ {C:.1f} · d^{{{delta:.2f}}}")
        self.log(f"  R² = {r2:.4f}")
        self.log(f"  N_c(5)_MP = {Ncs[list(ds).index(5)]:.0f}")

        self.check("N_c power law R² > 0.99", r2 > 0.99)


if __name__ == "__main__":
    MarchenkoPastur().execute()
