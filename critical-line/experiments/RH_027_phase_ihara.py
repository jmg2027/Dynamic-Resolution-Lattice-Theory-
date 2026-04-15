"""
RH_027: Phase Ihara Zeta — Primitive Cycles as Primes
======================================================

Dead end to avoid: RH_020-021 tried Ihara COEFFICIENTS = mu(n).
Failed because walk length != integer index.

NEW APPROACH: Use COMPLEX-VALUED Gram entries G_ij (not |G_ij|^2)
to define a "Phase Ihara Zeta" where primitive cycles carry phases.

Key idea:
  - Primitive cycles on the Gram graph <-> primes
  - Phase product along cycle c: Theta(c) = arg(prod G_{edges})
  - If phases are uniform on S^1 -> Mobius randomness follows

Tests:
  1. Phase Ihara zeta zeros: do they lie on a critical circle?
  2. Phase uniformity of primitive cycles
  3. Phase product correlations: multiplicative structure?
  4. Comparison: complex weights vs Born weights (|G|^2)
  5. Primitive cycle counting vs PNT

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class PhaseIhara(Experiment):
    ID = "RH_027"
    TITLE = "Phase Ihara zeta"

    def run(self):
        self.test1_phase_ihara_zeros()
        self.test2_cycle_phase_uniformity()
        self.test3_multiplicative_structure()
        self.test4_complex_vs_born()
        self.test5_pnt_scaling()

    # -- Helpers --------------------------------------------------

    @staticmethod
    def _make_gram(N, d=D, seed=42):
        """Random Gram matrix of N unit vectors in C^d."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        return psi @ psi.conj().T

    @staticmethod
    def _edge_adjacency(G):
        """Build the directed edge adjacency matrix for non-backtracking walks.

        For a complete graph on N vertices, directed edges are (i,j) with i!=j.
        Edge (i,j) -> (j,k) is allowed iff k != i (no backtracking).
        Weight of transition = G_{j,k} (complex inner product).
        """
        N = G.shape[0]
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_edges = len(edges)
        edge_idx = {e: idx for idx, e in enumerate(edges)}

        B = np.zeros((n_edges, n_edges), dtype=complex)
        for idx1, (i, j) in enumerate(edges):
            for k in range(N):
                if k != i and k != j:  # no backtrack, no self-loop
                    idx2 = edge_idx.get((j, k))
                    if idx2 is not None:
                        B[idx1, idx2] = G[j, k]
        return B, edges

    @staticmethod
    def _closed_walk_phases(G, max_len=6):
        """Compute Tr(G_directed^ell) to get sum of phases of
        closed non-backtracking walks of length ell.

        Actually: use Tr(B^ell) where B is edge adjacency."""
        B, _ = PhaseIhara._edge_adjacency(G)
        traces = {}
        Bk = np.eye(B.shape[0], dtype=complex)
        for ell in range(1, max_len + 1):
            Bk = Bk @ B
            traces[ell] = np.trace(Bk)
        return traces

    # -- Test 1: Phase Ihara zeros --------------------------------

    def test1_phase_ihara_zeros(self):
        """Compute zeros of the Phase Ihara zeta (complex weights).

        Ihara zeta: Z_G(u)^{-1} = det(I - u*B) where B is
        the edge adjacency matrix with complex weights.
        Zeros of Z_G(u)^{-1} = eigenvalues of B inverted: u = 1/lambda.
        """
        self.log("\n=== Test 1: Phase Ihara Zeta Zeros ===")
        self.log("  Z_G(u)^{-1} = det(I - u*B), B = complex edge adjacency")

        N_values = [6, 8, 10]
        for N in N_values:
            G = self._make_gram(N)
            B, edges = self._edge_adjacency(G)
            n_edges = len(edges)
            self.log(f"\n  N={N}: {n_edges} directed edges, "
                     f"B is {n_edges}x{n_edges}")

            # Eigenvalues of B
            evals = np.linalg.eigvals(B)
            # Zeros of Z^{-1} are at u = 1/lambda (for lambda != 0)
            nonzero = evals[np.abs(evals) > 1e-10]
            zeros = 1.0 / nonzero

            # Check: do zeros cluster on a circle |u| = r?
            radii = np.abs(zeros)
            r_mean = np.mean(radii)
            r_std = np.std(radii)

            # Phase distribution of zeros
            phases = np.angle(zeros)

            self.log(f"  Non-zero evals: {len(nonzero)}/{n_edges}")
            self.log(f"  Zero radii: mean={r_mean:.4f}, std={r_std:.4f}")
            self.log(f"  |u| range: [{np.min(radii):.4f}, "
                     f"{np.max(radii):.4f}]")

            # Critical circle: for Ramanujan, |u| = 1/sqrt(q)
            # For our graph, q ~ d-1 = 4, so |u| ~ 1/2
            q_eff = D - 1  # = 4
            r_crit = 1.0 / np.sqrt(q_eff)
            frac_near_crit = np.mean(np.abs(radii - r_crit) < 0.15)
            self.log(f"  Critical circle |u|=1/sqrt({q_eff})={r_crit:.4f}")
            self.log(f"  Fraction within 0.15 of critical: "
                     f"{frac_near_crit:.2%}")

        self.check("Phase Ihara zeros computed for N=6,8,10", True)

    # -- Test 2: Phase uniformity of cycles -----------------------

    def test2_cycle_phase_uniformity(self):
        """Are the phase products of closed NB walks uniform on S^1?

        Tr(B^ell) = sum of (product of G_ij along each closed NB walk).
        Each term is a complex number. The PHASE of this sum tells us
        about phase cancellation (uniformity -> small |Tr|/count).
        """
        self.log("\n=== Test 2: Cycle Phase Uniformity ===")
        self.log("  Tr(B^ell) = sum of phase products along closed walks")
        self.log("  If phases uniform: |Tr(B^ell)| << Tr(|B|^ell)")

        N = 8
        n_trials = 50
        max_len = 8

        self.log(f"\n  {'ell':>4} | {'|Tr(B^ell)|':>12} | "
                 f"{'Tr(|B|^ell)':>12} | {'ratio':>8} | "
                 f"{'cancellation':>13}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*12}-+-{'-'*8}-+-{'-'*13}")

        avg_ratios = {}
        for ell in range(2, max_len + 1):
            abs_traces = []
            mag_traces = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                B, _ = self._edge_adjacency(G)
                B_abs = np.abs(B)

                Bk = np.linalg.matrix_power(B, ell)
                Bk_abs = np.linalg.matrix_power(B_abs, ell)

                abs_traces.append(np.abs(np.trace(Bk)))
                mag_traces.append(np.real(np.trace(Bk_abs)))

            mean_abs = np.mean(abs_traces)
            mean_mag = np.mean(mag_traces)
            ratio = mean_abs / mean_mag if mean_mag > 0 else 0
            cancel = 1 - ratio
            avg_ratios[ell] = ratio

            self.log(f"  {ell:4d} | {mean_abs:12.2f} | {mean_mag:12.2f} | "
                     f"{ratio:8.4f} | {cancel:13.1%}")

        # High cancellation = phases are close to uniform
        # For ℂ, expect ~69% cancellation (from RH_002)
        avg_cancel = 1 - np.mean(list(avg_ratios.values()))
        self.log(f"\n  Average cancellation: {avg_cancel:.1%}")
        self.log(f"  (RH_002 found 69% for single-step phases)")
        self.check("Phase cancellation > 50%", avg_cancel > 0.5)

    # -- Test 3: Multiplicative structure -------------------------

    def test3_multiplicative_structure(self):
        """Check if cycle phases have multiplicative structure.

        If cycle of length ab decomposes as products of cycles
        of length a and b, then:
          Phase(ab-cycle) ~ Phase(a-cycle) * Phase(b-cycle)

        This would be the analog of chi(mn) = chi(m)*chi(n).
        """
        self.log("\n=== Test 3: Multiplicative Phase Structure ===")
        self.log("  Does Phase(ell1*ell2 cycle) ~ Phase(ell1)*Phase(ell2)?")

        N = 8
        n_trials = 100
        G = self._make_gram(N, seed=42)
        B, edges = self._edge_adjacency(G)

        # Compare Tr(B^6) vs Tr(B^2) * Tr(B^3)
        # If multiplicative: Tr(B^6) ~ Tr(B^2) * Tr(B^3) / Tr(B^1)
        # (Not exactly, but phase correlation)

        pairs = [(2, 3), (2, 4), (3, 4), (2, 5)]
        self.log(f"\n  {'(a,b)':>7} | {'arg Tr(B^ab)':>14} | "
                 f"{'arg Tr(B^a)+arg Tr(B^b)':>24} | {'diff':>8}")
        self.log(f"  {'-'*7}-+-{'-'*14}-+-{'-'*24}-+-{'-'*8}")

        phase_diffs = []
        for seed in range(n_trials):
            G = self._make_gram(N, seed=seed)
            B, _ = self._edge_adjacency(G)

            for a, b in pairs:
                Ba = np.linalg.matrix_power(B, a)
                Bb = np.linalg.matrix_power(B, b)
                Bab = np.linalg.matrix_power(B, a * b)

                phase_a = np.angle(np.trace(Ba))
                phase_b = np.angle(np.trace(Bb))
                phase_ab = np.angle(np.trace(Bab))

                diff = phase_ab - (phase_a + phase_b)
                # Wrap to [-pi, pi]
                diff = (diff + np.pi) % (2 * np.pi) - np.pi
                phase_diffs.append(abs(diff))

        mean_diff = np.mean(phase_diffs)
        # If multiplicative: mean_diff << pi
        # If independent: mean_diff ~ pi/2
        self.log(f"\n  Mean |phase_ab - (phase_a + phase_b)| = "
                 f"{mean_diff:.4f}")
        self.log(f"  Random expectation: pi/2 = {np.pi/2:.4f}")
        self.log(f"  Multiplicative would give: << pi/2")

        is_multiplicative = mean_diff < np.pi / 2 * 0.8
        self.log(f"  Multiplicative structure: "
                 f"{'DETECTED' if is_multiplicative else 'NOT detected'}")
        self.check("Multiplicative test computed", True)

    # -- Test 4: Complex vs Born weights --------------------------

    def test4_complex_vs_born(self):
        """Compare Phase Ihara (complex G_ij) vs standard Ihara (|G_ij|^2).

        Key question: does the phase information in G_ij change the
        zero distribution compared to Born-weighted Ihara?
        """
        self.log("\n=== Test 4: Complex vs Born Ihara ===")
        self.log("  Phase Ihara: B[e1,e2] = G_{j,k} (complex)")
        self.log("  Born Ihara:  B[e1,e2] = |G_{j,k}|^2 (real)")

        N = 8
        n_trials = 30

        complex_radii_all = []
        born_radii_all = []

        for t in range(n_trials):
            G = self._make_gram(N, seed=t)

            # Complex edge adjacency
            B_c, edges = self._edge_adjacency(G)
            evals_c = np.linalg.eigvals(B_c)
            nz_c = evals_c[np.abs(evals_c) > 1e-10]
            radii_c = np.sort(1.0 / np.abs(nz_c))
            complex_radii_all.extend(radii_c)

            # Born edge adjacency (same structure, |G|^2 weights)
            G_born = np.abs(G) ** 2
            np.fill_diagonal(G_born, 0)
            B_b, _ = self._edge_adjacency_real(G_born)
            evals_b = np.linalg.eigvals(B_b)
            nz_b = evals_b[np.abs(evals_b) > 1e-10]
            radii_b = np.sort(1.0 / np.abs(nz_b))
            born_radii_all.extend(radii_b)

        complex_radii_all = np.array(complex_radii_all)
        born_radii_all = np.array(born_radii_all)

        self.log(f"\n  Complex Ihara zeros: {len(complex_radii_all)}")
        self.log(f"    |u| mean={np.mean(complex_radii_all):.4f}, "
                 f"std={np.std(complex_radii_all):.4f}")
        self.log(f"  Born Ihara zeros: {len(born_radii_all)}")
        self.log(f"    |u| mean={np.mean(born_radii_all):.4f}, "
                 f"std={np.std(born_radii_all):.4f}")

        # Key: complex Ihara should have TIGHTER concentration
        # because ℂ phases produce more cancellation
        ratio = np.std(complex_radii_all) / np.std(born_radii_all)
        self.log(f"\n  Std ratio (complex/born): {ratio:.3f}")
        self.log(f"  < 1 means complex phases help concentration")

        self.check("Complex vs Born comparison computed", True)

    @staticmethod
    def _edge_adjacency_real(W):
        """Edge adjacency for real-weighted graph (Born weights)."""
        N = W.shape[0]
        edges = [(i, j) for i in range(N) for j in range(N)
                 if i != j and W[i, j] > 0]
        n_edges = len(edges)
        edge_idx = {e: idx for idx, e in enumerate(edges)}

        B = np.zeros((n_edges, n_edges))
        for idx1, (i, j) in enumerate(edges):
            for k in range(N):
                if k != i:
                    idx2 = edge_idx.get((j, k))
                    if idx2 is not None:
                        B[idx1, idx2] = W[j, k]
        return B, edges

    # -- Test 5: PNT scaling of primitive cycles ------------------

    def test5_pnt_scaling(self):
        """Count primitive cycles and check PNT: pi(ell) ~ q^ell / ell.

        Use Mobius inversion on Tr(B^ell) to get primitive counts.
        """
        self.log("\n=== Test 5: PNT Scaling ===")
        self.log("  pi(ell) ~ q^ell / ell where q = spectral radius")

        N = 8
        max_len = 8
        n_trials = 30

        def mobius(n):
            if n == 1:
                return 1
            temp, factors = n, []
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
            return (-1) ** len(factors)

        self.log(f"\n  {'ell':>4} | {'|pi_G(ell)|':>12} | "
                 f"{'q^ell/ell':>12} | {'ratio':>8}")
        self.log(f"  {'-'*4}-+-{'-'*12}-+-{'-'*12}-+-{'-'*8}")

        for ell in range(2, max_len + 1):
            prim_counts = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                B, _ = self._edge_adjacency(G)

                # Closed NB walk counts via Tr(B^k)
                walks = {}
                Bk = np.eye(B.shape[0], dtype=complex)
                for k in range(1, ell + 1):
                    Bk = Bk @ B
                    walks[k] = np.trace(Bk)

                # Mobius inversion for primitive count
                total = 0
                for d in range(1, ell + 1):
                    if ell % d == 0:
                        mu = mobius(ell // d)
                        total += mu * walks.get(d, 0)
                prim_counts.append(np.abs(total / ell))

            mean_prim = np.mean(prim_counts)

            # Spectral radius as effective q
            G0 = self._make_gram(N, seed=0)
            B0, _ = self._edge_adjacency(G0)
            q_eff = np.max(np.abs(np.linalg.eigvals(B0)))
            pnt_pred = q_eff ** ell / ell

            ratio = mean_prim / pnt_pred if pnt_pred > 0 else 0

            self.log(f"  {ell:4d} | {mean_prim:12.1f} | "
                     f"{pnt_pred:12.1f} | {ratio:8.3f}")

        self.check("PNT scaling measured", True)


if __name__ == "__main__":
    PhaseIhara().execute()
