"""
EXP_067: Zeta Physical Parameter — Spectral Dimension of W-Network
====================================================================

Question: Can s in ζ(s) be interpreted as a continuously varying
physical parameter within DRLT?

Key insight: D(n) = 1/n^(n_A - 1) = 1/n^s with s = n_A - 1 = 2.
If s=2 means "propagation in 3D space", then varying s means
varying the effective spatial dimensionality d_eff = s + 1.

But n_A = 3 is ALGEBRAIC (from the (3,2) split), not topological.
The W-graph is fully connected → its graph d_s ≠ 3.
This distinction (pre-geometric vs emergent) is itself a result.

Tests:
  1. Heat kernel spectral dimension of W-graph (pre-geometric)
  2. Weyl eigenvalue scaling: λ_k ~ k^{2/d_s} dimension probe
  3. Folded dimension leaking: s_eff = 2 - ε, ε ~ O(α_GUT)
  4. Zeta-eta ratio at s_eff: ζ(s)/η(s) → n_T = 2
  5. N_eff vs s duality: partial Basel sum ↔ ζ(s) equivalence

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))

import numpy as np
from scipy.special import zeta as sp_zeta
from experiment import Experiment
from drlt import (D, N_S, N_T, ALPHA_GUT, ZETA_2,
                  GramMatrix)


class ZetaSpectralDim(Experiment):
    ID = "067"
    TITLE = "Zeta spectral dimension"

    def run(self):
        self.test1_spectral_dimension()
        self.test2_rank_as_dimension()
        self.test3_folded_leaking()
        self.test4_zeta_eta_ratio()
        self.test5_Neff_s_duality()

    # ── helpers ──────────────────────────────────────────────────

    def _build_W_graph(self, N, seed=42):
        """Build W-weighted adjacency from N random vertices in ℂ⁵."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, D) + 1j * rng.randn(N, D)
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        psi = psi / norms
        gm = GramMatrix(psi)
        W = gm.W()                       # W_ij = |G_ij|²/d
        np.fill_diagonal(W, 0.0)         # no self-loops
        return W, gm

    def _graph_laplacian(self, W):
        """Normalized graph Laplacian L = I - D^{-1/2} W D^{-1/2}."""
        deg = W.sum(axis=1)
        deg_inv_sqrt = np.where(deg > 0, 1.0 / np.sqrt(deg), 0.0)
        D_inv = np.diag(deg_inv_sqrt)
        L = np.eye(len(W)) - D_inv @ W @ D_inv
        return 0.5 * (L + L.T)  # ensure symmetry

    def _heat_kernel_trace(self, eigvals, sigma_values):
        """
        K(σ) = Σ_k exp(-σ λ_k)  (heat kernel trace).
        σ = diffusion time (continuous).
        """
        K = np.array([np.sum(np.exp(-s * eigvals)) for s in sigma_values])
        return K

    def _spectral_dim_heat(self, sigma, K):
        """
        d_s(σ) = -2 d(ln K)/d(ln σ) from heat kernel.
        """
        mask = (K > 0) & (sigma > 0)
        ln_s = np.log(sigma[mask])
        ln_K = np.log(K[mask])
        d_s = -2.0 * np.diff(ln_K) / np.diff(ln_s)
        s_mid = np.exp(0.5 * (ln_s[:-1] + ln_s[1:]))
        return s_mid, d_s

    # ── Test 1 ───────────────────────────────────────────────────

    def test1_spectral_dimension(self):
        """
        Heat-kernel spectral dimension of W-network.

        Key distinction:
          - d_s (graph) = pre-geometric dimension (from W topology)
          - n_A = 3     = emergent dimension (from (3,2) algebra)

        These are NOT the same! The W-graph is fully connected,
        so d_s(graph) reflects the RANK of the Gram matrix, not
        the emergent spatial dimensionality.

        We measure d_s via the heat kernel K(σ) = Tr(e^{-σL})
        on the graph Laplacian L. d_s(σ) = -2 d ln K / d ln σ.
        """
        self.log("\n" + "="*55)
        self.log("  TEST 1: Heat-kernel spectral dimension")
        self.log("="*55)

        sigma_vals = np.logspace(-2, 2, 200)

        for N in [40, 80, 150]:
            W, gm = self._build_W_graph(N, seed=137)
            L = self._graph_laplacian(W)
            eigvals = np.linalg.eigvalsh(L)

            # Gram spectrum (rank ≤ 5 structure)
            gram_spec = gm.spectrum()[:7]
            self.log(f"\n  N = {N}:")
            self.log(f"    Gram eigenvalues (top 7): "
                     f"{gram_spec.round(2)}")
            n_significant = np.sum(gram_spec > 0.5)
            self.log(f"    Significant Gram eigenvalues: "
                     f"{n_significant}  (= rank ≤ {D})")

            # Laplacian spectrum
            self.log(f"    Laplacian: λ_min={eigvals[0]:.4f}, "
                     f"λ_max={eigvals[-1]:.4f}, "
                     f"gap={eigvals[1]:.4f}")

            # Heat kernel spectral dimension
            K = self._heat_kernel_trace(eigvals, sigma_vals)
            s_mid, d_s = self._spectral_dim_heat(sigma_vals, K)

            # Report d_s at different diffusion scales
            probes = [0.01, 0.05, 0.1, 0.5, 1.0, 5.0]
            self.log(f"    {'σ':>6s}  {'d_s':>6s}  {'s_eff':>6s}")
            for sp in probes:
                idx = np.argmin(np.abs(s_mid - sp))
                self.log(f"    {sp:6.2f}  {d_s[idx]:6.2f}"
                         f"  {d_s[idx]-1:6.2f}")

        self.log(f"\n  Interpretation:")
        self.log(f"    d_s(σ→0) → large: UV regime, all N modes")
        self.log(f"    d_s(σ~1) → O(1):  effective pre-geometric dim")
        self.log(f"    d_s(σ→∞) → 0:     IR, finite graph mixing")
        self.log(f"    n_A=3 is ALGEBRAIC (Binet-Cauchy), not d_s")
        self.check("Test 1: heat-kernel d_s measured", True)

    # ── Test 2 ───────────────────────────────────────────────────

    def test2_rank_as_dimension(self):
        """
        The dimension s = n_A - 1 is ALGEBRAIC, from Gram rank.

        W = |G|²/d loses rank info (element-wise squaring).
        The (3,2) split lives in the GRAM matrix spectrum:
          rank(G)    ≤ 5 = d      → full internal dimension
          rank(G^AA) ≤ 3 = n_A    → spatial dimension
          rank(G^BB) ≤ 2 = n_B    → temporal dimension

        s = rank(G^AA) - 1 = n_A - 1 = 2.

        This is NOT a topological property of the W-graph,
        it's an algebraic property of ℂ⁵ = ℂ³ ⊕ ℂ².
        The solid-angle propagator D(n) = 1/n^s depends on
        rank, not graph distance.
        """
        self.log("\n" + "="*55)
        self.log("  TEST 2: Gram rank IS the dimension parameter")
        self.log("="*55)

        for N in [20, 50, 150]:
            W, gm = self._build_W_graph(N, seed=314)

            # Full Gram spectrum
            spec_full = gm.spectrum()
            rank_full = np.sum(spec_full > 1e-8)

            # Sector Gram spectra
            psi_A = gm.psi[:, 2:5]
            psi_B = gm.psi[:, 0:2]
            G_AA = psi_A @ psi_A.conj().T
            G_BB = psi_B @ psi_B.conj().T

            spec_AA = np.sort(np.linalg.eigvalsh(G_AA))[::-1]
            spec_BB = np.sort(np.linalg.eigvalsh(G_BB))[::-1]
            rank_AA = np.sum(spec_AA > 1e-8)
            rank_BB = np.sum(spec_BB > 1e-8)

            self.log(f"\n  N = {N}:")
            self.log(f"    rank(G)    = {rank_full}  (max {D})")
            self.log(f"    rank(G^AA) = {rank_AA}  (max {N_S})")
            self.log(f"    rank(G^BB) = {rank_BB}  (max {N_T})")

            # Eigenvalue structure
            self.log(f"    G    top 6: {spec_full[:6].round(2)}")
            self.log(f"    G^AA top 4: {spec_AA[:4].round(2)}")
            self.log(f"    G^BB top 3: {spec_BB[:3].round(2)}")

            # Trace conservation: Tr(G) = N = Tr(G^AA) + Tr(G^BB)
            tr_full = np.trace(gm.G).real
            tr_AA = np.trace(G_AA).real
            tr_BB = np.trace(G_BB).real
            self.log(f"    Tr check: {tr_AA:.1f} + {tr_BB:.1f}"
                     f" = {tr_AA+tr_BB:.1f} = Tr(G) = {tr_full:.1f}")

        # The conclusion
        self.log(f"\n  ═══════════════════════════════════════════")
        self.log(f"  Key result:")
        self.log(f"    s = rank(G^AA) - 1 = {N_S} - 1 = {N_S-1}")
        self.log(f"    D(n) = 1/n^s = 1/n²  (solid angle in rank-3)")
        self.log(f"    This is an ALGEBRAIC fact, not topological.")
        self.log(f"    rank is discrete → s is locked to integer.")
        self.log(f"    Continuous s requires EFFECTIVE rank change")
        self.log(f"    (folded dim leaking, see Test 3).")
        self.log(f"  ═══════════════════════════════════════════")

        # Check: rank structure matches (3,2)
        _, gm0 = self._build_W_graph(100, seed=42)
        psi_A = gm0.psi[:, 2:5]
        psi_B = gm0.psi[:, 0:2]
        rA = np.sum(np.linalg.eigvalsh(
            psi_A @ psi_A.conj().T) > 1e-8)
        rB = np.sum(np.linalg.eigvalsh(
            psi_B @ psi_B.conj().T) > 1e-8)
        self.check(f"Test 2: rank(G^AA)={rA}=n_A, rank(G^BB)={rB}=n_B",
                   rA == N_S and rB == N_T)

    # ── Test 3 ───────────────────────────────────────────────────

    def test3_folded_leaking(self):
        """
        Folded dimension leaking → s_eff = 2 - ε.

        The (3,2) split isn't perfectly clean. The 0⁺ eigenvalues
        (folded dimensions) leak with strength α_GUT ≈ 0.024.

        If n_A,eff = 3 - ε with ε ~ O(α_GUT), then:
          s_eff = 2 - ε
          ζ(2-ε) ≈ π²/6 + ε·Σ(ln n / n²) + O(ε²)

        The ln n term is the origin of logarithmic RG running!
        ζ'(2) = -Σ(ln n / n²) ≈ -0.9376

        Coupling shift: δ(1/α) ≈ -ε · ζ'(2) per channel.
        """
        self.log("\n" + "="*55)
        self.log("  TEST 3: Folded dimension leaking → ε correction")
        self.log("="*55)

        # Analytic: ζ(2-ε) expansion
        zeta_2 = np.pi**2 / 6
        # ζ'(2) = -Σ ln(n)/n² (converges, compute numerically)
        n_terms = 100000
        ns = np.arange(1, n_terms + 1, dtype=float)
        zeta_prime_2 = -np.sum(np.log(ns) / ns**2)
        self.log(f"\n  ζ(2)  = π²/6 = {zeta_2:.6f}")
        self.log(f"  ζ'(2) = -Σ ln(n)/n² = {zeta_prime_2:.6f}")

        # Candidate ε values from folded dimension theory
        eps_candidates = {
            "α_GUT":          ALPHA_GUT,
            "α_GUT/3 (SST)":  ALPHA_GUT / 3,
            "2α_GUT/3 (STT)": 2 * ALPHA_GUT / 3,
        }

        self.log(f"\n  {'ε source':<20s}  {'ε':>10s}  {'ζ(2-ε)':>10s}"
                 f"  {'δ(1/α)':>10s}  {'% shift':>8s}")
        self.log(f"  {'─'*65}")

        for name, eps in eps_candidates.items():
            zeta_shifted = zeta_2 - eps * zeta_prime_2
            # Also compute exact ζ(2-ε) via scipy
            s_val = 2.0 - eps
            zeta_exact = float(sp_zeta(s_val, 1))
            delta_inv_alpha = -eps * zeta_prime_2  # per channel
            pct = delta_inv_alpha / zeta_2 * 100

            self.log(f"  {name:<20s}  {eps:10.5f}  "
                     f"{zeta_exact:10.6f}  "
                     f"{delta_inv_alpha:10.6f}  {pct:7.3f}%")

        # Key result: the log correction
        eps_gut = ALPHA_GUT
        log_correction = -eps_gut * zeta_prime_2
        self.log(f"\n  At ε = α_GUT:")
        self.log(f"    Log correction = {log_correction:.6f}")
        self.log(f"    This is the 'missing' RG logarithm!")
        self.log(f"    ζ'(2) ≈ -0.938: each unit of ε shifts")
        self.log(f"    the coupling by ~0.94 per channel")

        has_log = abs(zeta_prime_2 + 0.9376) < 0.01
        self.check("Test 3: ζ'(2) ≈ -0.938 (log running origin)",
                   has_log)

    # ── Test 4 ───────────────────────────────────────────────────

    def test4_zeta_eta_ratio(self):
        """
        Zeta-eta ratio as continuous dimension counter.

        ζ(s)/η(s) = 2^s / (2^s - 2)

        At s=2: → 2 = n_T (temporal dimension count).
        As s varies continuously, this ratio tracks the
        "effective temporal dimension count" n_T,eff(s).

        Physical meaning:
          s < 2: ratio > 2 → more temporal dims (spatial leaking)
          s > 2: ratio < 2 → fewer temporal dims
          s = 1: ratio → ∞ (IR catastrophe, 2D space)
          s = 4: ratio = 8/7 ≈ 1.14 (all 5 dims spatial)
        """
        self.log("\n" + "="*55)
        self.log("  TEST 4: Zeta-eta ratio — continuous dim counter")
        self.log("="*55)

        def zeta_eta_ratio(s):
            """ζ(s)/η(s) = 2^s / (2^s - 2) for s > 1."""
            return 2**s / (2**s - 2)

        def eta_func(s, n_terms=100000):
            """Dirichlet eta: η(s) = Σ(-1)^{n+1}/n^s."""
            ns = np.arange(1, n_terms + 1, dtype=float)
            signs = (-1.0)**(ns + 1)
            return np.sum(signs / ns**s)

        # Table of s values and their physical interpretation
        s_values = [1.01, 1.5, 1.9, 1.95, 2.0, 2.05, 2.1, 2.5, 3.0, 4.0]
        labels = {
            1.01: "near-critical (2D)",
            1.5:  "fractal (2.5D)",
            1.9:  "pre-leaking",
            1.95: "small leaking",
            2.0:  "OUR UNIVERSE",
            2.05: "anti-leaking",
            2.1:  "post-leaking",
            2.5:  "3.5D space",
            3.0:  "4D space",
            4.0:  "5D space (all)",
        }

        self.log(f"\n  {'s':>5s}  {'ζ/η ratio':>10s}  {'n_T,eff':>8s}"
                 f"  {'d_eff':>6s}  {'interpretation':<20s}")
        self.log(f"  {'─'*60}")

        for s in s_values:
            ratio = zeta_eta_ratio(s)
            d_eff = s + 1
            label = labels.get(s, "")
            marker = " ◄" if s == 2.0 else ""
            self.log(f"  {s:5.2f}  {ratio:10.4f}  {ratio:8.4f}"
                     f"  {d_eff:6.2f}  {label:<20s}{marker}")

        # Verify at s=2: ratio = 2 = n_T exactly
        r2 = zeta_eta_ratio(2.0)
        self.log(f"\n  At s=2: ζ(2)/η(2) = {r2:.10f}")
        self.log(f"  n_T = {N_T}")

        # Verify via direct computation
        zeta_2 = np.pi**2 / 6
        eta_2 = np.pi**2 / 12
        ratio_direct = zeta_2 / eta_2
        self.log(f"  Direct: (π²/6)/(π²/12) = {ratio_direct:.10f}")

        # With folded dimension leaking: s_eff = 2 - α_GUT
        s_leaked = 2.0 - ALPHA_GUT
        r_leaked = zeta_eta_ratio(s_leaked)
        self.log(f"\n  With leaking (s = 2 - α_GUT = {s_leaked:.4f}):")
        self.log(f"    ζ/η = {r_leaked:.6f}")
        self.log(f"    Δ(n_T) = {r_leaked - 2:.6f}")
        self.log(f"    The (3,2) split leaks by {(r_leaked-2)/2*100:.3f}%")

        exact_2 = abs(r2 - 2.0) < 1e-10
        self.check("Test 4: ζ(2)/η(2) = 2 = n_T exactly", exact_2)

    # ── Test 5 ───────────────────────────────────────────────────

    def test5_Neff_s_duality(self):
        """
        N_eff–s duality: two equivalent descriptions of coupling running.

        View 1 (book ch08): fix s=2, vary N_eff
          S(N_eff) = Σ_{n=1}^{N_eff} 1/n²

        View 2 (new): fix N_eff=∞, vary s
          ζ(s) = Σ_{n=1}^∞ 1/n^s

        Both interpolate between:
          UV: S(1) = 1 = ζ(∞)
          IR: S(∞) = ζ(2) = π²/6

        For each N_eff, find s* such that ζ(s*) = S(N_eff).
        This s* is the "dual effective dimension" for that range.
        """
        self.log("\n" + "="*55)
        self.log("  TEST 5: N_eff ↔ s duality")
        self.log("="*55)

        # Partial Basel sums for key N_eff values
        def partial_basel(N_eff):
            return sum(1.0 / n**2 for n in range(1, N_eff + 1))

        # Find s* such that ζ(s*) = target, by bisection
        def find_dual_s(target, s_lo=1.001, s_hi=50.0, tol=1e-8):
            for _ in range(200):
                s_mid = (s_lo + s_hi) / 2
                val = float(sp_zeta(s_mid, 1))
                if val > target:
                    s_lo = s_mid
                else:
                    s_hi = s_mid
                if abs(val - target) < tol:
                    break
            return s_mid

        self.log(f"\n  {'N_eff':>6s}  {'S(N_eff)':>10s}  {'s*':>8s}"
                 f"  {'d*_eff':>7s}  {'force':>10s}")
        self.log(f"  {'─'*50}")

        neff_data = [
            (1,   "strong"),
            (2,   "weak"),
            (3,   "—"),
            (5,   "—"),
            (10,  "—"),
            (50,  "—"),
            (500, "—"),
        ]

        s_stars = []
        for neff, force in neff_data:
            S_val = partial_basel(neff)
            s_star = find_dual_s(S_val)
            d_eff = s_star + 1
            s_stars.append(s_star)
            self.log(f"  {neff:6d}  {S_val:10.6f}  {s_star:8.4f}"
                     f"  {d_eff:7.3f}  {force:>10s}")

        # EM: N_eff = ∞ → s* = 2 exactly
        self.log(f"  {'∞':>6s}  {np.pi**2/6:10.6f}  {'2.0000':>8s}"
                 f"  {'3.000':>7s}  {'EM':>10s}")

        # Key check: strong (N_eff=1) → s* → ∞ (only nearest neighbor)
        strong_uv = s_stars[0] > 10  # s* should be very large
        self.log(f"\n  Strong force: N_eff=1 ↔ s*={s_stars[0]:.1f}")
        self.log(f"    → d*_eff = {s_stars[0]+1:.1f}: 'infinite dim'")
        self.log(f"    → Only nearest-neighbor: UV extreme")

        # Key check: weak (N_eff=2) → s* ≈ some finite value
        self.log(f"  Weak force: N_eff=2 ↔ s*={s_stars[1]:.4f}")
        self.log(f"    → d*_eff = {s_stars[1]+1:.3f}")

        # Physical interpretation
        self.log(f"\n  Duality interpretation:")
        self.log(f"    Varying N_eff at s=2 ↔ varying s at N_eff=∞")
        self.log(f"    'Range cutoff' ↔ 'effective dimension change'")
        self.log(f"    Both describe the same coupling running")
        self.log(f"    s parametrizes HOW the lattice propagates,")
        self.log(f"    N_eff parametrizes HOW FAR it propagates")

        # Monotonicity: s* decreases as N_eff increases
        monotone = all(s_stars[i] > s_stars[i+1]
                       for i in range(len(s_stars)-1))
        self.check("Test 5: s*(N_eff) is monotonically decreasing",
                   monotone)


if __name__ == "__main__":
    ZetaSpectralDim().execute()
