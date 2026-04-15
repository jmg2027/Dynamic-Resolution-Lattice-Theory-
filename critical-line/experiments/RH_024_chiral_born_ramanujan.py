"""
RH_024: Chiral Projection Born-Ramanujan (Gap 3 Resolution)
============================================================

CRITICAL: Previous Born-Ramanujan (RH_008-011) assumed rank(G)=5.
Correct picture: rank(G) = d_ind > 5, chiral content is π₅Gπ₅†.

Questions:
  1. Does KR decomposition work for G_c = π₅Gπ₅†?
  2. Does the MP formula with p_eff=d(d-1) apply to G_c?
  3. What is N_c for the chiral projection?
  4. How does ρ_chiral compare to ρ_full?

Key: G_c has rank ≤ 5 regardless of d_ind, but the
projected vectors are NOT unit vectors (||π₅ψ||² = 5/d_ind < 1).
This changes the normalization of W_c = |G_c|².

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class ChiralBornRamanujan(Experiment):
    ID = "RH_024"
    TITLE = "Chiral projection Born-Ramanujan"

    def run(self):
        self.test1_projection_structure()
        self.test2_khatri_rao_chiral()
        self.test3_ramanujan_vs_dind()
        self.test4_Nc_chiral()

    def _make_chiral(self, N, d_ind, seed=42):
        """Full G in ℂ^{d_ind}, then project to chiral ℂ⁵."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d_ind) + 1j * rng.randn(N, d_ind)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        psi_c = psi[:, :5]  # chiral projection (NOT renormalized)
        G_c = psi_c @ psi_c.conj().T
        W_c = np.abs(G_c)**2
        np.fill_diagonal(W_c, 0.0)
        return W_c, G_c, psi_c

    def _ramanujan_ratio(self, W):
        eigs = np.sort(np.linalg.eigvalsh(W))[::-1]
        d_eff = W.sum(axis=1).mean()
        bound = 2 * np.sqrt(max(d_eff - 1, 0.01))
        return eigs[1] / bound if bound > 0 else 0

    # ── Test 1: Projection Structure ─────────────────────

    def test1_projection_structure(self):
        """How chiral projection changes the Gram structure."""
        self.log("\n═══ Test 1: Chiral Projection Structure ═══")

        N = 50
        d_values = [5, 7, 9, 11, 15, 21]

        self.log(f"\n  {'d_ind':>5} | {'⟨||π₅ψ||²⟩':>12} | {'5/d_ind':>8} | "
                 f"{'rank(G_c)':>9} | {'Tr(G_c)/N':>10}")
        self.log(f"  {'-'*5}-+-{'-'*12}-+-{'-'*8}-+-"
                 f"{'-'*9}-+-{'-'*10}")

        for d_ind in d_values:
            _, G_c, psi_c = self._make_chiral(N, d_ind, seed=42)
            norms_sq = np.sum(np.abs(psi_c)**2, axis=1)
            rank = np.linalg.matrix_rank(G_c, tol=1e-8)
            tr = np.real(np.trace(G_c)) / N

            self.log(f"  {d_ind:>5} | {np.mean(norms_sq):>12.5f} | "
                     f"{5/d_ind:>8.5f} | {rank:>9} | {tr:>10.5f}")

        self.check("Projection structure mapped", True)

    # ── Test 2: KR for Chiral Projection ─────────────────

    def test2_khatri_rao_chiral(self):
        """Does W_c + diag = Φ_c†Φ_c still hold?"""
        self.log("\n═══ Test 2: Khatri-Rao for G_c ═══")
        self.log("  φ_c = π₅ψ ⊗ conj(π₅ψ) ∈ ℂ^25")

        N = 30
        d_ind = 11

        _, G_c, psi_c = self._make_chiral(N, d_ind, seed=42)

        # KR: φ_i = psi_c_i ⊗ conj(psi_c_i)
        Phi_c = np.zeros((N, 25), dtype=complex)
        for i in range(N):
            Phi_c[i] = np.kron(psi_c[i], psi_c[i].conj())

        W_c_kr = np.real(Phi_c @ Phi_c.conj().T)
        W_c_direct = np.abs(G_c)**2

        err = np.max(np.abs(W_c_direct - W_c_kr))
        self.log(f"  d_ind={d_ind}, N={N}")
        self.log(f"  max|W_c - Φ_c†Φ_c| = {err:.2e}")
        self.log(f"  (KR still exact for projected vectors)")

        # Note: diag(W_c) = ||π₅ψ_i||⁴ ≠ 1 (not unit vectors!)
        diag_vals = np.diag(W_c_direct)
        self.log(f"  diag(W_c): mean={np.mean(diag_vals):.5f}, "
                 f"expected (5/d_ind)²={25/d_ind**2:.5f}")

        self.check("KR holds for chiral projection", err < 1e-10)

    # ── Test 3: Ramanujan vs d_ind ───────────────────────

    def test3_ramanujan_vs_dind(self):
        """ρ_chiral as function of d_ind (total dimension)."""
        self.log("\n═══ Test 3: ρ_chiral vs d_ind ═══")
        self.log("  Key: as d_ind grows, projection captures less norm")

        N = 50
        d_values = [5, 7, 9, 11, 15, 21]
        n_trials = 50

        self.log(f"\n  {'d_ind':>5} | {'⟨ρ_c⟩':>7} | {'5/d_ind':>8} | "
                 f"{'d_eff':>7} | {'Ram%':>5}")
        self.log(f"  {'-'*5}-+-{'-'*7}-+-{'-'*8}-+-"
                 f"{'-'*7}-+-{'-'*5}")

        for d_ind in d_values:
            rhos = []
            d_effs = []
            n_ram = 0
            for t in range(n_trials):
                W_c, _, _ = self._make_chiral(N, d_ind, seed=t+d_ind*100)
                rho = self._ramanujan_ratio(W_c)
                rhos.append(rho)
                d_effs.append(W_c.sum(axis=1).mean())
                if rho < 1:
                    n_ram += 1

            self.log(f"  {d_ind:>5} | {np.mean(rhos):>7.4f} | "
                     f"{5/d_ind:>8.4f} | {np.mean(d_effs):>7.2f} | "
                     f"{n_ram/n_trials:>4.0%}")

        self.check("ρ_chiral measured for all d_ind", True)

    # ── Test 4: N_c for Chiral Projection ────────────────

    def test4_Nc_chiral(self):
        """Find N_c where ρ_chiral = 1 for each d_ind."""
        self.log("\n═══ Test 4: N_c(d_ind) for Chiral Projection ═══")

        d_values = [5, 7, 9, 11, 15]
        n_trials = 30

        self.log(f"\n  {'d_ind':>5} | {'N_c(chiral)':>11} | "
                 f"{'N_c(rank5)':>10} | {'ratio':>6}")
        self.log(f"  {'-'*5}-+-{'-'*11}-+-{'-'*10}-+-{'-'*6}")

        for d_ind in d_values:
            # Binary search for N_c
            lo, hi = 20, 2000
            for _ in range(12):
                mid = (lo + hi) // 2
                rhos = []
                for t in range(n_trials):
                    W_c, _, _ = self._make_chiral(mid, d_ind, seed=t+d_ind*200)
                    rhos.append(self._ramanujan_ratio(W_c))
                if np.mean(rhos) < 1:
                    lo = mid
                else:
                    hi = mid
            Nc_chiral = (lo + hi) // 2

            # For comparison: pure rank-5 (d_ind=5)
            Nc_rank5 = 350  # from RH_011

            ratio = Nc_chiral / Nc_rank5 if Nc_rank5 > 0 else 0
            self.log(f"  {d_ind:>5} | {Nc_chiral:>11} | "
                     f"{Nc_rank5:>10} | {ratio:>6.2f}")

        self.check("N_c(chiral) computed", True)


if __name__ == "__main__":
    ChiralBornRamanujan().execute()
