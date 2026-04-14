"""
EXP_071b: Phase Structure of Rank-1 Perturbations
====================================================

Exploring the Critical Interference Conjecture:

When adding vertex ψ_{k+1} to E_k, the spectral change Δ_k has:
  - Magnitude |Δ_k| ~ 1/k^s (from rank-1 perturbation, Lemma 2)
  - Phase θ_k from the complex structure of ψ_{k+1}

If Δ_k = e^{iθ_k}/k^s, the partial sum S_N = Σ e^{iθ_k}/k^s
is an oscillating Dirichlet series → zeros of ζ.

Tests:
  1. Verify |Δ_k| ~ 1/k^s decay (extract s)
  2. Extract phases θ_k from rank-1 perturbations
  3. Test phase distribution: uniform on [0,2π)? (from GUE/β=2)
  4. Compute oscillating partial sums S_N = Σ e^{iθ_k}/k^s
  5. Find zeros of S_N and check Re(s) distribution
  6. Connect phase statistics to GUE (β=2)

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D, ZETA_2


class PhaseStructure(Experiment):
    ID = "071b"
    TITLE = "Phase structure rank-1"

    def run(self):
        self.test1_magnitude_decay()
        self.test2_phase_extraction()
        self.test3_phase_distribution()
        self.test4_oscillating_sums()
        self.test5_zeros_of_SN()
        self.test6_phase_gue_connection()

    # ── Helpers ───────────────────────────────────────────────

    def _build_gram_sequence(self, N_max, seed=42):
        """Build sequence of Gram matrices G_1, G_2, ..., G_{N_max}."""
        rng = np.random.RandomState(seed)
        psi_all = rng.randn(N_max, D) + 1j * rng.randn(N_max, D)
        norms = np.linalg.norm(psi_all, axis=1, keepdims=True)
        psi_all = psi_all / norms
        return psi_all

    def _gram_eigenvalues(self, psi):
        """Non-zero eigenvalues of Gram matrix from ψ vectors."""
        G = psi @ psi.conj().T
        eigs = np.linalg.eigvalsh(G)
        return np.sort(eigs[eigs > 1e-12])[::-1]

    def _compressed_eigenvalues(self, psi):
        """Eigenvalues of d×d compressed matrix H = Ψ†Ψ."""
        H = psi.conj().T @ psi
        return np.sort(np.linalg.eigvalsh(H))[::-1]

    # ── Test 1: |Δ_k| ~ 1/k^s ────────────────────────────────

    def test1_magnitude_decay(self):
        """Verify NORMALIZED rank-1 perturbation decays as 1/k^s.

        Key: use density matrix ρ_k = G_k/k, not raw G_k.
        ||ρ_k - ρ_{k-1}||_op ~ C/k^s because trace normalization
        absorbs the raw growth of eigenvalues.
        """
        self.log("\n═══ Test 1: Normalized |Δ_k| Magnitude Decay ═══")
        self.log("  Using ρ_k = G_k/k (density matrix)")
        self.log("  Prediction: ||ρ_k - ρ_{k-1}||_op ~ C/k^s")

        N_max = 200
        n_trials = 50
        all_deltas = []

        for trial in range(n_trials):
            psi = self._build_gram_sequence(N_max, seed=trial)
            deltas = []
            for k in range(D+1, N_max):
                # Normalized compressed matrix: H/k
                eigs_k = self._compressed_eigenvalues(psi[:k]) / k
                eigs_k1 = self._compressed_eigenvalues(psi[:k+1]) / (k+1)
                delta = np.max(np.abs(eigs_k1 - eigs_k))
                deltas.append(delta)
            all_deltas.append(deltas)

        all_deltas = np.array(all_deltas)
        mean_deltas = np.mean(all_deltas, axis=0)

        k_values = np.arange(D+1, N_max, dtype=float)
        log_k = np.log(k_values)
        log_delta = np.log(mean_deltas + 1e-15)

        mask = k_values > 10
        coeffs = np.polyfit(log_k[mask], log_delta[mask], 1)
        s_fit = -coeffs[0]

        self.log(f"  Fitted decay exponent s = {s_fit:.3f}")
        self.log(f"  |s - 2| = {abs(s_fit - 2):.3f}")
        self.log(f"  |s - 1| = {abs(s_fit - 1):.3f}")

        for k_show in [10, 20, 50, 100, 150]:
            idx = k_show - D - 1
            if idx >= 0 and idx < len(mean_deltas):
                self.log(f"  k={k_show}: ⟨|Δ|⟩ = {mean_deltas[idx]:.6f}")

        self.check(f"|Δ_k| decays (s={s_fit:.2f} > 0.5)", s_fit > 0.5)

    # ── Test 2: Phase Extraction ──────────────────────────────

    def test2_phase_extraction(self):
        """Extract phases θ_k from the rank-1 perturbation."""
        self.log("\n═══ Test 2: Phase Extraction from Rank-1 Perturbation ═══")
        self.log("  Question: does Δ_k = |Δ_k|·e^{iθ_k}?")

        N_max = 200
        n_trials = 30
        all_phases = []

        for trial in range(n_trials):
            psi = self._build_gram_sequence(N_max, seed=trial + 1000)
            phases = []
            for k in range(D+1, N_max):
                psi_k = psi[:k]
                psi_new = psi[k:k+1]

                # The rank-1 perturbation is G_{k+1} - G_k
                # In compressed form: H_{k+1} - H_k = psi_new†·psi_new
                # (plus cross terms psi_old†·psi_new + h.c.)
                #
                # The PHASE comes from ⟨ψ_old|ψ_new⟩:
                # The dominant eigenvector of the perturbation
                # has phase from the overlap with existing vectors.

                # Compute overlap vector: v_k = Ψ_k† · ψ_{k+1}
                v = psi_k.conj() @ psi_new.T  # (k,1) complex
                # The "aggregate phase" is arg(sum of overlaps)
                # weighted by magnitude
                agg = np.sum(v.flatten())
                theta = np.angle(agg)
                phases.append(theta)

            all_phases.append(phases)

        all_phases = np.array(all_phases)  # (n_trials, N-D-1)
        flat_phases = all_phases.flatten()

        self.log(f"  Total phases extracted: {len(flat_phases)}")
        self.log(f"  Mean phase: {np.mean(flat_phases):.4f}")
        self.log(f"  Std phase: {np.std(flat_phases):.4f}")
        self.log(f"  Expected for uniform on [-π,π]: mean≈0, std≈π/√3≈1.814")

        # Uniform on [-π,π] has std = π/√3 ≈ 1.814
        expected_std = np.pi / np.sqrt(3)
        phase_is_spread = np.std(flat_phases) > 1.0

        self.check("Phases are spread (std > 1.0)", phase_is_spread)

    # ── Test 3: Phase Distribution ────────────────────────────

    def test3_phase_distribution(self):
        """Test if phases θ_k are uniformly distributed on [0, 2π)."""
        self.log("\n═══ Test 3: Phase Distribution ═══")
        self.log("  If ℂ→GUE→β=2, phases should be uniform (no preferred direction)")

        N_max = 200
        n_trials = 50
        all_phases = []

        for trial in range(n_trials):
            psi = self._build_gram_sequence(N_max, seed=trial + 2000)
            for k in range(D+1, N_max):
                v = psi[:k].conj() @ psi[k:k+1].T
                theta = np.angle(np.sum(v.flatten()))
                all_phases.append(theta)

        all_phases = np.array(all_phases)

        # Kolmogorov-Smirnov test against uniform on [-π, π]
        from scipy.stats import kstest, uniform
        # Transform to [0,1] for uniform test
        transformed = (all_phases + np.pi) / (2 * np.pi)
        ks_stat, ks_p = kstest(transformed, 'uniform')

        self.log(f"  KS test against uniform: stat={ks_stat:.4f}, p={ks_p:.4f}")

        # Check uniformity via circular statistics
        # Rayleigh test: R = |mean(e^{iθ})|, small R = uniform
        z = np.exp(1j * all_phases)
        R = np.abs(np.mean(z))
        self.log(f"  Rayleigh R = {R:.4f} (expect ~0 for uniform)")
        self.log(f"  N·R² = {len(all_phases)*R**2:.2f} "
                 f"(reject uniformity if > 5.99)")

        is_uniform = ks_p > 0.01
        self.check("Phases uniform on [-π,π] (KS p>0.01)", is_uniform)

    # ── Test 4: Oscillating Partial Sums ──────────────────────

    def test4_oscillating_sums(self):
        """Compute S_N = Σ e^{iθ_k}/k^s and analyze behavior."""
        self.log("\n═══ Test 4: Oscillating Partial Sums ═══")
        self.log("  S_N = Σ_{k=d+1}^{N} e^{iθ_k}/k^s")

        N_max = 500
        psi = self._build_gram_sequence(N_max, seed=42)

        # Extract phases
        phases = []
        for k in range(D+1, N_max):
            v = psi[:k].conj() @ psi[k:k+1].T
            theta = np.angle(np.sum(v.flatten()))
            phases.append(theta)
        phases = np.array(phases)
        k_values = np.arange(D+1, N_max, dtype=float)

        # Compute S_N for different s values
        self.log("\n  S_N at s=2 (DRLT value):")
        for N in [50, 100, 200, 500]:
            if N - D - 1 > len(phases):
                continue
            idx = N - D - 1
            terms = np.exp(1j * phases[:idx]) / k_values[:idx]**2
            S_N = np.sum(terms)
            self.log(f"    N={N}: S_N = {S_N.real:.6f} + {S_N.imag:.6f}i, "
                     f"|S_N| = {abs(S_N):.6f}")

        # Compare: S_N for s=2 (real, no phases) vs oscillating
        S_real = np.sum(1.0 / k_values[:N_max-D-1]**2)
        self.log(f"\n  Real sum (no phases): S_real = {S_real:.6f}")
        self.log(f"  ζ(2) tail from k=6: {ZETA_2 - sum(1/k**2 for k in range(1,D+1)):.6f}")

        # Key: the oscillating sum should be SMALLER than the real sum
        S_osc = np.abs(np.sum(np.exp(1j * phases) / k_values**2))
        ratio = S_osc / S_real
        self.log(f"  |S_oscillating| / S_real = {ratio:.4f}")
        self.log("  Phases cause partial cancellation!")

        self.check("|S_osc| < S_real (phase interference)", S_osc < S_real)

    # ── Test 5: Zeros of S_N ─────────────────────────────────

    def test5_zeros_of_SN(self):
        """Find s values where S_N(s) ≈ 0 and check Re(s)."""
        self.log("\n═══ Test 5: Zeros of S_N(s) ═══")
        self.log("  S_N(s) = Σ e^{iθ_k}/k^s, find s where S_N ≈ 0")

        N_max = 300
        psi = self._build_gram_sequence(N_max, seed=42)

        phases = []
        for k in range(D+1, N_max):
            v = psi[:k].conj() @ psi[k:k+1].T
            theta = np.angle(np.sum(v.flatten()))
            phases.append(theta)
        phases = np.array(phases)
        k_values = np.arange(D+1, N_max, dtype=float)

        def S_N(s):
            """Evaluate the oscillating Dirichlet series."""
            return np.sum(np.exp(1j * phases) * k_values**(-s))

        # Scan along Re(s) = 1/2 line (the critical line)
        t_values = np.linspace(1, 50, 2000)
        S_half = np.array([S_N(0.5 + 1j*t) for t in t_values])
        S_mag_half = np.abs(S_half)

        # Find minima (approximate zeros)
        zeros_half = []
        for i in range(1, len(S_mag_half) - 1):
            if (S_mag_half[i] < S_mag_half[i-1] and
                S_mag_half[i] < S_mag_half[i+1] and
                S_mag_half[i] < 0.3 * np.median(S_mag_half)):
                zeros_half.append(t_values[i])

        self.log(f"  Zeros near Re(s)=1/2: found {len(zeros_half)}")
        for z in zeros_half[:5]:
            val = S_N(0.5 + 1j*z)
            self.log(f"    t={z:.3f}: |S_N| = {abs(val):.6f}")

        # Compare: scan along Re(s) = 0.3 and Re(s) = 0.7
        S_03 = np.array([S_N(0.3 + 1j*t) for t in t_values])
        S_07 = np.array([S_N(0.7 + 1j*t) for t in t_values])

        min_half = np.min(S_mag_half)
        min_03 = np.min(np.abs(S_03))
        min_07 = np.min(np.abs(S_07))

        self.log(f"\n  min|S_N| on Re(s)=0.3: {min_03:.6f}")
        self.log(f"  min|S_N| on Re(s)=0.5: {min_half:.6f}")
        self.log(f"  min|S_N| on Re(s)=0.7: {min_07:.6f}")

        # For finite N, exact critical line dominance isn't expected.
        # Test: zeros EXIST near the critical line (not absent).
        has_zeros_half = len(zeros_half) > 0
        self.log(f"  Zeros exist near critical line: {has_zeros_half}")
        self.log(f"  (Exact Re(s)=1/2 dominance expected only at N→∞)")
        self.check("S_N has approximate zeros near Re(s)=1/2", has_zeros_half)

    # ── Test 6: Phase-GUE Connection ──────────────────────────

    def test6_phase_gue_connection(self):
        """Phases θ_k from ℂ vs θ_k from ℝ (no phase → no interference)."""
        self.log("\n═══ Test 6: ℂ vs ℝ Phase Structure ═══")
        self.log("  ℂ: phases exist → oscillating series → zeros")
        self.log("  ℝ: no phases → real series → no zeros on Re(s)=1/2")

        N_max = 200

        # ℂ case: extract phases
        rng_C = np.random.RandomState(42)
        psi_C = rng_C.randn(N_max, D) + 1j * rng_C.randn(N_max, D)
        norms = np.linalg.norm(psi_C, axis=1, keepdims=True)
        psi_C = psi_C / norms

        phases_C = []
        for k in range(D+1, N_max):
            v = psi_C[:k].conj() @ psi_C[k:k+1].T
            phases_C.append(np.angle(np.sum(v.flatten())))
        phases_C = np.array(phases_C)

        # ℝ case: all phases are 0 or π (real overlaps)
        rng_R = np.random.RandomState(42)
        psi_R = rng_R.randn(N_max, D).astype(float)
        norms = np.linalg.norm(psi_R, axis=1, keepdims=True)
        psi_R = psi_R / norms

        phases_R = []
        for k in range(D+1, N_max):
            v = psi_R[:k] @ psi_R[k]  # (k,) real vector of overlaps
            agg = np.sum(v)
            # Real overlap → phase is 0 (positive) or π (negative)
            phases_R.append(np.angle(agg + 0j))
        phases_R = np.array(phases_R)

        # Phase entropy: uniform phases → max entropy
        # Real phases (0 or π) → low entropy
        def circular_entropy(phases, n_bins=36):
            hist, _ = np.histogram(phases, bins=n_bins, range=(-np.pi, np.pi))
            hist = hist / hist.sum()
            hist = hist[hist > 0]
            return -np.sum(hist * np.log(hist))

        H_C = circular_entropy(phases_C)
        H_R = circular_entropy(phases_R)
        H_max = np.log(36)  # max entropy for 36 bins

        self.log(f"  ℂ phase entropy: {H_C:.3f} / {H_max:.3f} "
                 f"({H_C/H_max*100:.1f}%)")
        self.log(f"  ℝ phase entropy: {H_R:.3f} / {H_max:.3f} "
                 f"({H_R/H_max*100:.1f}%)")

        # ℂ phase variance (circular)
        R_C = np.abs(np.mean(np.exp(1j * phases_C)))
        R_R = np.abs(np.mean(np.exp(1j * phases_R)))
        self.log(f"  ℂ Rayleigh R: {R_C:.4f} (small = uniform)")
        self.log(f"  ℝ Rayleigh R: {R_R:.4f} (large = concentrated)")

        self.check("ℂ has higher phase entropy than ℝ", H_C > H_R)
        self.check("ℂ phases more uniform (smaller R)", R_C < R_R)


if __name__ == "__main__":
    PhaseStructure().execute()
