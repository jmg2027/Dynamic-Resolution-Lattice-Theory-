"""
RH_051: Unfolding Test — Is the Poisson Result Genuine?
=========================================================

RH_050 found: Im(s) spacings are Poisson, not GUE.
But the unfolding was WRONG (global mean only).

The Ihara map λ → Im(s) has Jacobian:
  d(Im(s))/dλ = 1/(log(q)·√(4q-λ²))

This DIVERGES at λ = ±2√q (band edges), creating
a density pile-up that looks like clustering (Poisson).

CRITICAL QUESTION: After proper unfolding, is it still Poisson?
- If YES: genuine discovery (GUE lives in eigenvalue space)
- If NO: artifact of bad unfolding (GUE is universal)

Tests:
  1. Control: raw eigenvalue ⟨r⟩ (should be GUE ~0.60)
  2. Control: CDF-unfolded eigenvalue ⟨r⟩ (should be GUE)
  3. Raw Im(s) ⟨r⟩ (was 0.44 in RH_050)
  4. THE KEY: CDF-unfolded Im(s) ⟨r⟩
  5. Band-edge exclusion: remove top/bottom 10% eigenvalues
  6. Spacing distribution after proper unfolding
  7. Pair correlation after proper unfolding

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class UnfoldingTest(Experiment):
    ID = "RH_051"
    TITLE = "Unfolding test for GUE vs Poisson"

    def run(self):
        self.test1_eigenvalue_r()
        self.test2_ims_raw_vs_unfolded()
        self.test3_band_edge_exclusion()
        self.test4_unfolded_spacing()
        self.test5_unfolded_pair_correlation()
        self.test6_verdict()

    @staticmethod
    def _gram_data(N, d, seed=42):
        """Return eigenvalues and Im(s) from Born-weighted Gram."""
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        G = psi @ psi.conj().T
        W = np.abs(G)**2
        np.fill_diagonal(W, 0)
        evals = np.sort(np.real(np.linalg.eigvals(W)))
        # Non-trivial eigenvalues (exclude largest = Perron)
        q_eff = evals[-1]
        nt_evals = evals[:-1]  # ascending order
        # Map to Im(s)
        log_q = np.log(q_eff) if q_eff > 1 else 1.0
        ims = []
        for lam in nt_evals:
            disc = lam**2 - 4*q_eff
            if disc < 0 and abs(lam) > 1e-12:
                re_u = lam / (2*q_eff)
                im_u = np.sqrt(-disc) / (2*q_eff)
                arg_u = np.arctan2(im_u, re_u)
                ims.append(-arg_u / log_q)
        return nt_evals, np.sort(ims), q_eff

    @staticmethod
    def _unfold_cdf(levels):
        """Unfold via empirical CDF (rank-based).
        Maps levels to uniform density = 1."""
        n = len(levels)
        if n < 3:
            return levels.copy()
        sorted_idx = np.argsort(levels)
        unfolded = np.empty_like(levels, dtype=float)
        for rank, idx in enumerate(sorted_idx):
            unfolded[idx] = (rank + 0.5) / n * n
        return np.sort(unfolded)

    @staticmethod
    def _unfold_poly(levels, deg=5):
        """Unfold via polynomial fit to staircase N(E)."""
        n = len(levels)
        if n < deg + 2:
            return levels.copy()
        x = np.sort(levels)
        y = np.arange(1, n + 1)  # staircase
        coeffs = np.polyfit(x, y, deg)
        unfolded = np.polyval(coeffs, x)
        return unfolded

    @staticmethod
    def _r_ratio(levels):
        """Compute ⟨r⟩ from sorted levels."""
        spacings = np.diff(levels)
        if len(spacings) < 2:
            return float('nan')
        ratios = []
        for i in range(len(spacings) - 1):
            s1, s2 = spacings[i], spacings[i+1]
            if max(s1, s2) > 1e-15:
                ratios.append(min(s1, s2) / max(s1, s2))
        return np.mean(ratios) if ratios else float('nan')

    # == Test 1: Eigenvalue ⟨r⟩ (Control) ========================

    def test1_eigenvalue_r(self):
        """⟨r⟩ for raw eigenvalues. Should be GUE ~0.60.
        This is the CONTROL: if this isn't GUE, nothing will be."""
        self.log("\n=== Test 1: Eigenvalue ⟨r⟩ (Control) ===")
        self.log("  GUE=0.5996, GOE=0.5307, Poisson=0.3863\n")

        d = D
        n_trials = 300

        for N in [30, 50, 80, 120]:
            raw_rs, unf_rs = [], []
            for t in range(n_trials):
                evals, _, _ = self._gram_data(N, d, seed=t)
                if len(evals) < 5:
                    continue
                raw_rs.append(self._r_ratio(evals))
                unfolded = self._unfold_cdf(evals)
                unf_rs.append(self._r_ratio(unfolded))

            mr = np.nanmean(raw_rs)
            mu = np.nanmean(unf_rs)
            self.log(f"  N={N:3d}: raw ⟨r⟩={mr:.4f}, "
                     f"CDF-unfolded ⟨r⟩={mu:.4f}")

        self.check("Eigenvalue ⟨r⟩ computed", True)

    # == Test 2: Im(s) Raw vs Unfolded ==========================

    def test2_ims_raw_vs_unfolded(self):
        """THE KEY TEST.
        Compare ⟨r⟩ for:
          (a) raw Im(s) — was 0.44 in RH_050
          (b) CDF-unfolded Im(s)
          (c) polynomial-unfolded Im(s)

        If unfolding restores GUE → artifact.
        If still Poisson → genuine.
        """
        self.log("\n=== Test 2: Im(s) Raw vs Unfolded ⟨r⟩ ===")
        self.log("  THIS IS THE CRITICAL TEST\n")

        d = D
        n_trials = 300

        self.log(f"  {'N':>4} | {'raw':>8} | {'CDF':>8} | "
                 f"{'poly-5':>8} | {'eigenval':>8}")
        self.log(f"  {'-'*4}-+-{'-'*8}-+-{'-'*8}-+-"
                 f"{'-'*8}-+-{'-'*8}")

        for N in [30, 50, 80, 120]:
            raw_r, cdf_r, poly_r, eval_r = [], [], [], []
            for t in range(n_trials):
                evals, ims, q = self._gram_data(N, d, seed=t)
                if len(ims) < 5:
                    continue

                # Eigenvalue ⟨r⟩ (control)
                eval_r.append(self._r_ratio(evals))

                # Raw Im(s) ⟨r⟩
                raw_r.append(self._r_ratio(ims))

                # CDF-unfolded Im(s)
                ims_cdf = self._unfold_cdf(ims)
                cdf_r.append(self._r_ratio(ims_cdf))

                # Polynomial-unfolded Im(s)
                ims_poly = self._unfold_poly(ims, deg=5)
                poly_r.append(self._r_ratio(ims_poly))

            mr = np.nanmean(raw_r)
            mc = np.nanmean(cdf_r)
            mp = np.nanmean(poly_r)
            me = np.nanmean(eval_r)
            self.log(f"  {N:4d} | {mr:8.4f} | {mc:8.4f} | "
                     f"{mp:8.4f} | {me:8.4f}")

        self.log(f"\n  If CDF/poly ≈ 0.60 (GUE): artifact fixed.")
        self.log(f"  If CDF/poly ≈ 0.39-0.44 (Poisson): genuine.")
        self.check("Im(s) unfolding comparison done", True)

    # == Test 3: Band-Edge Exclusion =============================

    def test3_band_edge_exclusion(self):
        """The Ihara map singularity at λ = ±2√q causes pile-up.
        Remove eigenvalues in the outer 10%/20% and retest.

        If ⟨r⟩ improves → the singularity was the problem.
        """
        self.log("\n=== Test 3: Band-Edge Exclusion ===")

        d = D
        N = 80
        n_trials = 300

        for pct in [0, 5, 10, 20, 30]:
            all_r = []
            for t in range(n_trials):
                evals, ims, q = self._gram_data(N, d, seed=t)
                if len(ims) < 10:
                    continue
                # Exclude outer pct% from BOTH ends
                n = len(ims)
                lo = int(n * pct / 100)
                hi = n - lo
                if hi - lo < 5:
                    continue
                ims_trimmed = ims[lo:hi]
                all_r.append(self._r_ratio(ims_trimmed))

            mr = np.nanmean(all_r)
            closest = "GUE" if abs(mr-0.5996) < abs(mr-0.3863) \
                else "Poisson"
            self.log(f"  Exclude {pct:2d}%: ⟨r⟩ = {mr:.4f} → {closest}")

        self.check("Band-edge exclusion tested", True)

    # == Test 4: Unfolded Spacing Distribution ====================

    def test4_unfolded_spacing(self):
        """After CDF unfolding of Im(s), compute spacing distribution.
        Compare to Wigner surmise (GUE) and Poisson."""
        self.log("\n=== Test 4: Unfolded Spacing Distribution ===")

        d = D
        N = 80
        n_trials = 300
        all_spacings = []

        for t in range(n_trials):
            _, ims, _ = self._gram_data(N, d, seed=t)
            if len(ims) < 10:
                continue
            ims_unf = self._unfold_poly(ims, deg=5)
            s = np.diff(ims_unf)
            mean_s = np.mean(s)
            if mean_s > 0:
                all_spacings.extend(s / mean_s)

        spacings = np.array(all_spacings)
        self.log(f"  {len(spacings)} unfolded spacings from "
                 f"N={N}, {n_trials} trials\n")

        bins = np.linspace(0, 4, 21)
        hist, _ = np.histogram(spacings, bins=bins, density=True)
        centers = (bins[:-1] + bins[1:]) / 2

        wigner = (32/np.pi**2) * centers**2 * \
            np.exp(-4*centers**2/np.pi)
        poisson = np.exp(-centers)

        chi2_gue = np.sum((hist - wigner)**2 / (wigner + 0.01))
        chi2_poi = np.sum((hist - poisson)**2 / (poisson + 0.01))

        self.log(f"  {'s':>5} | {'P(s)':>8} | {'GUE':>8} | "
                 f"{'Poisson':>8}")
        self.log(f"  {'-'*5}-+-{'-'*8}-+-{'-'*8}-+-{'-'*8}")
        for i in range(0, len(centers), 2):
            self.log(f"  {centers[i]:5.2f} | {hist[i]:8.4f} | "
                     f"{wigner[i]:8.4f} | {poisson[i]:8.4f}")

        self.log(f"\n  χ²(GUE)={chi2_gue:.3f}, "
                 f"χ²(Poisson)={chi2_poi:.3f}")
        closer = "GUE" if chi2_gue < chi2_poi else "Poisson"
        self.log(f"  Closer to: {closer}")
        self.check(f"Unfolded spacing: {closer}",
                   chi2_gue < chi2_poi)

    # == Test 5: Unfolded Pair Correlation =======================

    def test5_unfolded_pair_correlation(self):
        """After unfolding, test pair correlation R₂(x).
        GUE: R₂(x) = 1 - (sin πx / πx)²."""
        self.log("\n=== Test 5: Unfolded Pair Correlation ===")

        d = D
        N = 80
        n_trials = 300
        all_diffs = []

        for t in range(n_trials):
            _, ims, _ = self._gram_data(N, d, seed=t)
            if len(ims) < 10:
                continue
            ims_unf = self._unfold_poly(ims, deg=5)
            s = np.diff(ims_unf)
            mean_s = np.mean(s)
            if mean_s <= 0:
                continue
            for i in range(len(ims_unf)):
                for j in range(i+1, min(i+6, len(ims_unf))):
                    d_ij = abs(ims_unf[j] - ims_unf[i]) / mean_s
                    if d_ij < 4:
                        all_diffs.append(d_ij)

        diffs = np.array(all_diffs)
        bins = np.linspace(0.01, 3.5, 14)
        hist, _ = np.histogram(diffs, bins=bins, density=True)
        centers = (bins[:-1] + bins[1:]) / 2

        mo = 1 - (np.sin(np.pi*centers)/(np.pi*centers))**2

        self.log(f"  {len(diffs)} unfolded pair diffs\n")
        self.log(f"  {'x':>5} | {'R₂(data)':>10} | "
                 f"{'GUE theory':>10}")
        self.log(f"  {'-'*5}-+-{'-'*10}-+-{'-'*10}")
        for i in range(len(centers)):
            self.log(f"  {centers[i]:5.2f} | {hist[i]:10.4f} | "
                     f"{mo[i]:10.4f}")

        # Level repulsion check
        small = diffs[diffs < 0.3]
        frac_small = len(small) / len(diffs)
        repulsion = frac_small < 0.10
        self.log(f"\n  P(x < 0.3) = {frac_small:.4f} "
                 f"({'repulsion ✓' if repulsion else 'no repulsion ✗'})")
        self.check("Unfolded pair correlation: level repulsion",
                   repulsion)

    # == Test 6: Verdict =========================================

    def test6_verdict(self):
        """Collect all evidence and state the verdict."""
        self.log("\n=== Test 6: VERDICT ===")
        self.log(f"")
        self.log(f"  Evidence collected from Tests 1-5.")
        self.log(f"  The question: Is 'GUE in eigenvalue space,")
        self.log(f"  Poisson in s-plane' genuine or artifact?\n")
        self.log(f"  Three possible outcomes:")
        self.log(f"  (A) Unfolding fixes → artifact. GUE universal.")
        self.log(f"  (B) Unfolding doesn't fix → GENUINE.")
        self.log(f"      GUE is a property of eigenvalues,")
        self.log(f"      not of mapped zeros.")
        self.log(f"  (C) Intermediate: partially fixes, indicating")
        self.log(f"      the map distorts correlations but doesn't")
        self.log(f"      completely destroy them.")
        self.log(f"")
        self.log(f"  Verdict is determined by Tests 2-5 above.")
        self.check("Analysis complete", True)


if __name__ == "__main__":
    UnfoldingTest().execute()
