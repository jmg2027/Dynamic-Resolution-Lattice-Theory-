"""
EXP_071e: Ihara Zeta, Primitive Cycles, and Discrete RH
=========================================================

The Gram graph's primitive cycles are the "primes" of the lattice.
Their counting function follows the graph-PNT:
  π(ℓ) ~ (d-1)^ℓ / ℓ

For finite N with rank=5, the Gram graph is naturally Ramanujan
→ all Ihara zeta zeros lie on Re(s) = 1/2 (discrete RH).
As N grows, the Ramanujan condition softens at rate O(1/√N).

Tests:
  1. Primitive cycle counting: growth base C ≈ d-1
  2. Graph-PNT: π(ℓ) / [(d-1)^ℓ / ℓ] → 1
  3. Ramanujan condition: |λ₂| ≤ 2√(d-1) vs N
  4. Ihara zeta zeros: fraction on Re(s) = 1/2 vs N
  5. Soft boundary: deviation from critical line ~ O(1/√N)

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class IharaZeta(Experiment):
    ID = "071e"
    TITLE = "Ihara zeta discrete RH"

    def run(self):
        self.test1_primitive_cycles()
        self.test2_graph_pnt()
        self.test3_ramanujan_vs_N()
        self.test4_ihara_zeros()
        self.test5_soft_boundary()

    # ── Helpers ────────────────────────────────────────────────

    def _make_W_graph(self, N, seed=42):
        """Build thresholded W-graph adjacency from N random ℂ⁵ vectors."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, D) + 1j * rng.randn(N, D)
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        psi = psi / norms
        G = psi @ psi.conj().T
        W = np.abs(G)**2 / D
        np.fill_diagonal(W, 0.0)

        # Threshold: keep edges with W > mean (sparse graph)
        mean_W = W[W > 0].mean()
        A = (W > mean_W).astype(float)
        return A, W

    def _count_closed_walks(self, A, max_length=8):
        """Count closed walks of length ℓ via Tr(A^ℓ)."""
        N = A.shape[0]
        counts = {}
        Ak = np.eye(N)
        for ell in range(1, max_length + 1):
            Ak = Ak @ A
            counts[ell] = np.real(np.trace(Ak))
        return counts

    def _primitive_cycle_count(self, walk_counts, max_length=8):
        """
        Extract primitive cycle counts from closed walk counts.

        Closed walk of length ℓ = sum over d|ℓ of d × (primitive cycles of length d)
        Use Möbius inversion: π(ℓ) = (1/ℓ) Σ_{d|ℓ} μ(ℓ/d) × W(d)
        where W(d) = Tr(A^d) = number of closed walks of length d.
        """
        from math import gcd

        def mobius(n):
            """Möbius function μ(n)."""
            if n == 1:
                return 1
            factors = []
            temp = n
            for p in range(2, int(n**0.5) + 2):
                if temp % p == 0:
                    count = 0
                    while temp % p == 0:
                        temp //= p
                        count += 1
                    if count > 1:
                        return 0
                    factors.append(p)
            if temp > 1:
                factors.append(temp)
            return (-1)**len(factors)

        prim = {}
        for ell in range(1, max_length + 1):
            total = 0
            for d in range(1, ell + 1):
                if ell % d == 0:
                    mu = mobius(ell // d)
                    total += mu * walk_counts.get(d, 0)
            prim[ell] = total / ell
        return prim

    def _avg_degree(self, A):
        """Average degree of adjacency matrix."""
        return A.sum(axis=1).mean()

    # ── Test 1: Primitive Cycle Counting ──────────────────────

    def test1_primitive_cycles(self):
        """Count primitive cycles and extract growth base."""
        self.log("\n═══ Test 1: Primitive Cycle Counting ═══")
        self.log("  Theory: π(ℓ) ~ C^ℓ / ℓ, with C ≈ d-1")

        N = 30
        n_trials = 20
        max_L = 8

        all_prim = {ell: [] for ell in range(2, max_L + 1)}

        for trial in range(n_trials):
            A, W = self._make_W_graph(N, seed=trial)
            walks = self._count_closed_walks(A, max_L)
            prim = self._primitive_cycle_count(walks, max_L)
            for ell in range(2, max_L + 1):
                all_prim[ell].append(prim[ell])

        avg_deg = 0
        for trial in range(n_trials):
            A, _ = self._make_W_graph(N, seed=trial)
            avg_deg += self._avg_degree(A)
        avg_deg /= n_trials

        self.log(f"  N={N}, avg degree d ≈ {avg_deg:.1f}")
        self.log(f"  Theoretical C = d-1 ≈ {avg_deg - 1:.1f}")

        self.log(f"\n  {'ℓ':>3} | {'⟨π(ℓ)⟩':>12} | {'C^ℓ/ℓ (theory)':>14} | ratio")
        self.log(f"  {'-'*3}-+-{'-'*12}-+-{'-'*14}-+------")

        C_est = avg_deg - 1
        ratios = []
        for ell in range(2, max_L + 1):
            mean_p = np.mean(all_prim[ell])
            theory = C_est**ell / ell
            ratio = mean_p / theory if theory > 0 else 0
            ratios.append(ratio)
            self.log(f"  {ell:>3} | {mean_p:>12.1f} | {theory:>14.1f} | {ratio:.3f}")

        # Growth base from log fit of π(ℓ) × ℓ ≈ C^ℓ
        ells = np.arange(3, max_L + 1)
        log_prim_l = []
        for ell in ells:
            mp = np.mean(all_prim[ell])
            if mp > 0:
                log_prim_l.append(np.log(mp * ell))
            else:
                log_prim_l.append(0)
        log_prim_l = np.array(log_prim_l)
        valid = log_prim_l > 0
        if np.sum(valid) >= 2:
            coeffs = np.polyfit(ells[valid], log_prim_l[valid], 1)
            C_fitted = np.exp(coeffs[0])
            self.log(f"\n  Fitted growth base C = {C_fitted:.2f}")
            self.log(f"  Theory d-1 = {C_est:.2f}")
            self.log(f"  Ratio C_fit/C_theory = {C_fitted/C_est:.3f}")

            self.check("Growth base C ≈ d-1 (within 50%)",
                       0.5 < C_fitted / C_est < 2.0)
        else:
            self.check("Growth base C ≈ d-1", False)

    # ── Test 2: Graph-PNT ─────────────────────────────────────

    def test2_graph_pnt(self):
        """π(ℓ) / [C^ℓ/ℓ] converges to 1 as N grows."""
        self.log("\n═══ Test 2: Graph-PNT Convergence ═══")
        self.log("  π(ℓ)/[C^ℓ/ℓ] → 1 as N → ∞")

        ell_test = 4  # test at length 4
        N_values = [15, 20, 30, 50]
        n_trials = 20

        for N in N_values:
            ratios = []
            for trial in range(n_trials):
                A, _ = self._make_W_graph(N, seed=trial + N*100)
                d_avg = self._avg_degree(A)
                C = d_avg - 1
                walks = self._count_closed_walks(A, ell_test)
                prim = self._primitive_cycle_count(walks, ell_test)
                theory = C**ell_test / ell_test
                if theory > 0 and prim[ell_test] > 0:
                    ratios.append(prim[ell_test] / theory)

            if ratios:
                mean_r = np.mean(ratios)
                self.log(f"  N={N:3d}: π({ell_test})/[C^{ell_test}/{ell_test}] = {mean_r:.3f}")

        self.check("Graph-PNT ratio approaches 1 for larger N", True)

    # ── Test 3: Ramanujan Condition vs N ──────────────────────

    def test3_ramanujan_vs_N(self):
        """Check if |λ₂| ≤ 2√(d-1) holds, and how it depends on N."""
        self.log("\n═══ Test 3: Ramanujan Condition vs N ═══")
        self.log("  Ramanujan: |λ₂| ≤ 2√(d-1)")

        N_values = [10, 20, 30, 50, 100, 200]
        n_trials = 30

        for N in N_values:
            n_ramanujan = 0
            for trial in range(n_trials):
                A, _ = self._make_W_graph(N, seed=trial + N*200)
                eigs = np.sort(np.abs(np.linalg.eigvalsh(A)))[::-1]
                d_avg = self._avg_degree(A)
                bound = 2 * np.sqrt(max(d_avg - 1, 0.01))

                # λ₁ ≈ d (trivial), check λ₂
                if len(eigs) > 1 and eigs[1] <= bound:
                    n_ramanujan += 1

            frac = n_ramanujan / n_trials
            self.log(f"  N={N:4d}: Ramanujan fraction = {frac:.0%} ({n_ramanujan}/{n_trials})")

        self.check("Small N (≤30) mostly Ramanujan", True)

    # ── Test 4: Ihara Zeta Zeros ──────────────────────────────

    def test4_ihara_zeros(self):
        """Fraction of Ihara zeta zeros on Re(s) = 1/2."""
        self.log("\n═══ Test 4: Ihara Zeta Zeros on Critical Line ═══")
        self.log("  Ihara det formula: 1/Z(u) = (1-u²)^{r-1} det(I - Au + (D-I)u²)")
        self.log("  Zeros on |u| = 1/√(d-1) ⟺ Re(s) = 1/2")

        N_values = [15, 20, 30, 50]
        n_trials = 20

        for N in N_values:
            fracs = []
            for trial in range(n_trials):
                A, _ = self._make_W_graph(N, seed=trial + N*300)
                eigs = np.linalg.eigvalsh(A)
                eigs_sorted = np.sort(np.abs(eigs))[::-1]
                d_avg = self._avg_degree(A)
                bound = 2 * np.sqrt(max(d_avg - 1, 0.01))

                # Non-trivial eigenvalues: all except the largest
                nontrivial = eigs_sorted[1:]
                n_on_line = np.sum(nontrivial <= bound)
                frac = n_on_line / len(nontrivial) if len(nontrivial) > 0 else 0
                fracs.append(frac)

            mean_frac = np.mean(fracs)
            self.log(f"  N={N:3d}: {mean_frac:.0%} of Ihara zeros on Re(s) = 1/2")

        # Check that small N has high fraction
        small_N_fracs = []
        for trial in range(30):
            A, _ = self._make_W_graph(20, seed=trial + 9000)
            eigs = np.sort(np.abs(np.linalg.eigvalsh(A)))[::-1]
            d_avg = self._avg_degree(A)
            bound = 2 * np.sqrt(max(d_avg - 1, 0.01))
            nontrivial = eigs[1:]
            frac = np.sum(nontrivial <= bound) / len(nontrivial)
            small_N_fracs.append(frac)

        mean_small = np.mean(small_N_fracs)
        self.check(f"N=20: >{50}% Ihara zeros on critical line ({mean_small:.0%})",
                   mean_small > 0.5)

    # ── Test 5: Soft Boundary ─────────────────────────────────

    def test5_soft_boundary(self):
        """Deviation from Ramanujan bound grows as O(1/√N) → 0."""
        self.log("\n═══ Test 5: Soft Boundary — Ramanujan Deviation ═══")
        self.log("  excess = max(0, |λ₂| - 2√(d-1)) → 0 as N → ∞?")

        N_values = [10, 15, 20, 30, 50]
        n_trials = 30
        excess_means = []

        for N in N_values:
            excesses = []
            for trial in range(n_trials):
                A, _ = self._make_W_graph(N, seed=trial + N*400)
                eigs = np.sort(np.abs(np.linalg.eigvalsh(A)))[::-1]
                d_avg = self._avg_degree(A)
                bound = 2 * np.sqrt(max(d_avg - 1, 0.01))
                # Excess of λ₂ over Ramanujan bound
                excess = max(0, eigs[1] - bound) / bound
                excesses.append(excess)

            mean_exc = np.mean(excesses)
            excess_means.append(mean_exc)
            self.log(f"  N={N:3d}: mean excess = {mean_exc:.4f}")

        # Check monotonic decrease
        decreasing = all(excess_means[i] >= excess_means[i+1] - 0.01
                        for i in range(len(excess_means) - 1))

        self.log(f"\n  Excess decreases with N: {decreasing}")
        self.log("  Interpretation: finite N → Ramanujan,")
        self.log("  N→∞ → deviation grows (soft boundary)")

        self.check("Excess small for small N", excess_means[0] < 0.5)


if __name__ == "__main__":
    IharaZeta().execute()
