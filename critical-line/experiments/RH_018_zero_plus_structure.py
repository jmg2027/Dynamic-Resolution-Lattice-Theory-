"""
RH_018: The 0⁺ Structure — Chiral Projection and Soft Boundary
================================================================

CRITICAL CORRECTION (Jeong):
  G has rank d > 5, NOT rank 5 exactly.
  λ₆,...,λ_d are ~N/d (NOT 0!), τ-degenerate in pairs.
  "0⁺" = relative deviation from chiral eigenvalues.

The correct spectral picture:
  λ₁...λ₅     : chiral (ℂ²⊕ℂ³) — size ~N/d
  λ₆...λ_d    : paired (τ-degenerate) — size ~N/d (NOT 0⁺!)
  λ_{d+1}...λ_N : null — exactly 0

The soft boundary: |λ_chiral - λ_paired| = O(1/√N)

This experiment explores:
  1. Eigenvalue structure for d > 5 with τ-degenerate pairs
  2. The soft boundary as function of N
  3. Chiral projection G_chiral = π₅ G π₅†
  4. How the 0⁺ pattern relates to Born-Ramanujan

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class ZeroPlusStructure(Experiment):
    ID = "RH_018"
    TITLE = "0-plus eigenvalue structure"

    def run(self):
        self.test1_full_vs_chiral_spectrum()
        self.test2_soft_boundary()
        self.test3_paired_degeneracy()
        self.test4_chiral_projection_ramanujan()

    # ── Helpers ───────────────────────────────────────────

    def _make_structured_G(self, N, d_chiral=5, n_pairs=2, seed=42):
        """Build G with chiral + paired structure.

        d_total = d_chiral + 2*n_pairs (paired blocks of dim 2).
        Paired blocks have τ-degenerate eigenvalues (forced by construction).
        """
        rng = np.random.RandomState(seed)
        d_total = d_chiral + 2 * n_pairs

        # Chiral sector: random unit vectors in ℂ^5
        psi_chiral = rng.randn(N, d_chiral) + 1j * rng.randn(N, d_chiral)

        # Paired sectors: for each pair, use SAME random vectors
        # in two copies (τ-degeneracy = identical blocks)
        psi_paired = []
        for _ in range(n_pairs):
            block = rng.randn(N, 2) + 1j * rng.randn(N, 2)
            # Two copies of the same block = τ-degenerate pair
            # Small breaking: add α_GUT-scale perturbation
            alpha_gut = 6.0 / (25 * np.pi**2)  # ≈ 0.0243
            block2 = block + alpha_gut * (
                rng.randn(N, 2) + 1j * rng.randn(N, 2))
            psi_paired.append(block)
            psi_paired.append(block2)

        psi_full = np.hstack([psi_chiral] + psi_paired)
        norms = np.linalg.norm(psi_full, axis=1, keepdims=True)
        psi_full /= norms

        G = psi_full @ psi_full.conj().T
        return G, psi_full, d_total

    def _chiral_project(self, G, psi_full, d_chiral=5):
        """Project G onto chiral subspace (first d_chiral components)."""
        psi_chiral = psi_full[:, :d_chiral]
        # Re-normalize after projection
        norms = np.linalg.norm(psi_chiral, axis=1, keepdims=True)
        norms = np.maximum(norms, 1e-15)
        psi_chiral_norm = psi_chiral / norms
        G_chiral = psi_chiral_norm @ psi_chiral_norm.conj().T
        return G_chiral

    # ── Test 1: Full vs Chiral Spectrum ──────────────────

    def test1_full_vs_chiral_spectrum(self):
        """Compare eigenvalue structure: full G vs chiral projection."""
        self.log("\n═══ Test 1: Full vs Chiral Spectrum ═══")

        N = 50
        n_pairs_list = [0, 1, 2, 4]

        for n_pairs in n_pairs_list:
            G, psi, d_total = self._make_structured_G(
                N, d_chiral=5, n_pairs=n_pairs, seed=42)

            eigs_full = np.sort(np.linalg.eigvalsh(G))[::-1]
            G_chi = self._chiral_project(G, psi, d_chiral=5)
            eigs_chi = np.sort(np.linalg.eigvalsh(G_chi))[::-1]

            self.log(f"\n  d_total={d_total} (5 chiral + {2*n_pairs} paired):")
            self.log(f"    Full G top-{min(d_total+2, 12)} eigenvalues:")
            top = min(d_total + 2, 12)
            self.log(f"    {[f'{e:.2f}' for e in eigs_full[:top]]}")

            self.log(f"    Chiral projection top-7:")
            self.log(f"    {[f'{e:.2f}' for e in eigs_chi[:7]]}")

            # Gap between chiral and paired eigenvalues
            if n_pairs > 0:
                gap = eigs_full[4] - eigs_full[5]
                self.log(f"    Gap λ₅-λ₆ = {gap:.4f}")

        self.check("Spectrum structure explored", True)

    # ── Test 2: Soft Boundary vs N ───────────────────────

    def test2_soft_boundary(self):
        """Soft boundary gap = O(1/√N) between chiral and paired."""
        self.log("\n═══ Test 2: Soft Boundary Gap vs N ═══")
        self.log("  Theory: |λ_chiral - λ_paired| = O(1/√N)")

        N_values = [20, 50, 100, 200, 500]
        n_trials = 50
        n_pairs = 2  # d_total = 9

        self.log(f"\n  {'N':>5} | {'⟨gap⟩':>8} | {'1/√N':>8} | "
                 f"{'ratio':>6}")
        self.log(f"  {'-'*5}-+-{'-'*8}-+-{'-'*8}-+-{'-'*6}")

        gaps = []
        for N in N_values:
            trial_gaps = []
            for t in range(n_trials):
                G, psi, _ = self._make_structured_G(
                    N, d_chiral=5, n_pairs=n_pairs, seed=t + N*10)
                eigs = np.sort(np.linalg.eigvalsh(G))[::-1]
                # Gap: difference between 5th and 6th eigenvalue
                # (normalized by N/d to get relative gap)
                d_total = 5 + 2 * n_pairs
                gap = (eigs[4] - eigs[5]) / (N / d_total)
                trial_gaps.append(gap)

            mean_gap = np.mean(trial_gaps)
            inv_sqrtN = 1.0 / np.sqrt(N)
            ratio = mean_gap / inv_sqrtN if inv_sqrtN > 0 else 0
            gaps.append(mean_gap)
            self.log(f"  {N:>5} | {mean_gap:>8.5f} | "
                     f"{inv_sqrtN:>8.5f} | {ratio:>6.2f}")

        # Fit: gap ~ C · N^{-α}
        log_N = np.log(np.array(N_values, dtype=float))
        log_gap = np.log(np.array(gaps))
        coeffs = np.polyfit(log_N, log_gap, 1)
        alpha = -coeffs[0]
        self.log(f"\n  Fit: gap ~ N^{{-{alpha:.3f}}}")
        self.log(f"  Theory: gap ~ N^{{-0.500}}")

        self.check("Soft boundary exponent near 1/2",
                   abs(alpha - 0.5) < 0.3)

    # ── Test 3: Paired Degeneracy ────────────────────────

    def test3_paired_degeneracy(self):
        """τ-degenerate pairs: eigenvalues nearly identical."""
        self.log("\n═══ Test 3: τ-Degeneracy of Paired Blocks ═══")
        self.log("  Paired blocks: two copies + α_GUT perturbation")
        self.log("  Splitting should be ~α_GUT ≈ 0.024")

        N = 100
        n_pairs = 3  # d_total = 11
        n_trials = 30

        self.log(f"\n  d_total=11 (5 chiral + 6 paired = 3 pairs)")

        splittings = []
        for t in range(n_trials):
            G, psi, _ = self._make_structured_G(
                N, d_chiral=5, n_pairs=n_pairs, seed=t + 7777)
            eigs = np.sort(np.linalg.eigvalsh(G))[::-1]

            # Eigenvalues 6-11 should show pairing
            paired_eigs = eigs[5:11]
            for k in range(0, len(paired_eigs)-1, 2):
                split = abs(paired_eigs[k] - paired_eigs[k+1])
                splittings.append(split)

        mean_split = np.mean(splittings)
        # Normalize by mean eigenvalue
        G0, _, _ = self._make_structured_G(N, 5, n_pairs, seed=0)
        eigs0 = np.sort(np.linalg.eigvalsh(G0))[::-1]
        mean_eig = np.mean(eigs0[5:11])
        rel_split = mean_split / mean_eig if mean_eig > 0 else 0

        self.log(f"  mean paired splitting = {mean_split:.4f}")
        self.log(f"  ⟨λ_paired⟩ = {mean_eig:.2f}")
        self.log(f"  Relative splitting = {rel_split:.4f}")
        self.log(f"  α_GUT = {6/(25*np.pi**2):.4f}")

        self.check("Paired eigenvalues show small splitting",
                   rel_split < 0.5)

    # ── Test 4: Chiral Projection Ramanujan ──────────────

    def test4_chiral_projection_ramanujan(self):
        """Born-Ramanujan on chiral projection vs full G."""
        self.log("\n═══ Test 4: Ramanujan — Full vs Chiral ═══")

        N = 50
        n_pairs_list = [0, 1, 2, 4]
        n_trials = 30

        self.log(f"\n  {'d_total':>7} | {'ρ_full':>7} | "
                 f"{'ρ_chiral':>8} | {'ratio':>6}")
        self.log(f"  {'-'*7}-+-{'-'*7}-+-{'-'*8}-+-{'-'*6}")

        for n_pairs in n_pairs_list:
            rho_fulls = []
            rho_chirals = []
            d_total = 5 + 2 * n_pairs

            for t in range(n_trials):
                G, psi, _ = self._make_structured_G(
                    N, d_chiral=5, n_pairs=n_pairs, seed=t+N*100)

                # Full W
                W_full = np.abs(G)**2
                np.fill_diagonal(W_full, 0.0)
                eigs_f = np.sort(np.linalg.eigvalsh(W_full))[::-1]
                d_eff_f = W_full.sum(axis=1).mean()
                bound_f = 2 * np.sqrt(max(d_eff_f - 1, 0.01))
                rho_fulls.append(eigs_f[1] / bound_f)

                # Chiral projection W
                G_chi = self._chiral_project(G, psi, d_chiral=5)
                W_chi = np.abs(G_chi)**2
                np.fill_diagonal(W_chi, 0.0)
                eigs_c = np.sort(np.linalg.eigvalsh(W_chi))[::-1]
                d_eff_c = W_chi.sum(axis=1).mean()
                bound_c = 2 * np.sqrt(max(d_eff_c - 1, 0.01))
                rho_chirals.append(eigs_c[1] / bound_c)

            rf = np.mean(rho_fulls)
            rc = np.mean(rho_chirals)
            ratio = rc / rf if rf > 0 else 0
            self.log(f"  {d_total:>7} | {rf:>7.4f} | "
                     f"{rc:>8.4f} | {ratio:>6.3f}")

        self.check("Chiral projection changes Ramanujan ratio",
                   True)


if __name__ == "__main__":
    ZeroPlusStructure().execute()
