"""
RH_029: Phase Ihara — Finding the Critical Circle
===================================================

RH_027 showed Phase Ihara zeros don't cluster at |u| = 1/sqrt(4).
This experiment finds the ACTUAL critical circle by:
  1. Histogram of |u| for Phase Ihara zeros
  2. Identify the dominant radius (peak of histogram)
  3. Check if it relates to DRLT constants
  4. Compare across N values
  5. Fraction of zeros on the dominant circle vs N

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment
from drlt import D


class CriticalCircle(Experiment):
    ID = "RH_029"
    TITLE = "Phase Ihara critical circle"

    def run(self):
        self.test1_zero_histogram()
        self.test2_dominant_radius()
        self.test3_drlt_constants()
        self.test4_N_dependence()

    # -- Helpers (from RH_027) ------------------------------------

    @staticmethod
    def _make_gram(N, d=D, seed=42):
        rng = np.random.RandomState(seed)
        psi = rng.randn(N, d) + 1j * rng.randn(N, d)
        psi /= np.linalg.norm(psi, axis=1, keepdims=True)
        return psi @ psi.conj().T

    @staticmethod
    def _edge_adjacency(G):
        N = G.shape[0]
        edges = [(i, j) for i in range(N) for j in range(N) if i != j]
        n_edges = len(edges)
        edge_idx = {e: idx for idx, e in enumerate(edges)}
        B = np.zeros((n_edges, n_edges), dtype=complex)
        for idx1, (i, j) in enumerate(edges):
            for k in range(N):
                if k != i and k != j:
                    idx2 = edge_idx.get((j, k))
                    if idx2 is not None:
                        B[idx1, idx2] = G[j, k]
        return B, edges

    @staticmethod
    def _get_zeros(G):
        """Get Ihara zeros u = 1/lambda from edge adjacency."""
        B, _ = CriticalCircle._edge_adjacency(G)
        evals = np.linalg.eigvals(B)
        nonzero = evals[np.abs(evals) > 1e-10]
        return 1.0 / nonzero

    # -- Test 1: Zero histogram -----------------------------------

    def test1_zero_histogram(self):
        """Histogram of |u| for many Gram realizations."""
        self.log("\n=== Test 1: Zero radius histogram ===")

        N = 8
        n_trials = 50
        all_radii = []

        for t in range(n_trials):
            G = self._make_gram(N, seed=t)
            zeros = self._get_zeros(G)
            all_radii.extend(np.abs(zeros))

        all_radii = np.array(all_radii)
        self.log(f"  N={N}, {n_trials} trials, {len(all_radii)} zeros")

        # Histogram in bins
        bins = np.linspace(0, 5, 26)
        counts, edges = np.histogram(all_radii, bins=bins)
        centers = (edges[:-1] + edges[1:]) / 2

        self.log(f"\n  {'|u| bin':>10} | {'count':>6} | {'frac':>6} | bar")
        self.log(f"  {'-'*10}-+-{'-'*6}-+-{'-'*6}-+----")
        total = len(all_radii)
        peak_count = 0
        peak_center = 0
        for c, cnt in zip(centers, counts):
            frac = cnt / total
            bar = '#' * int(frac * 80)
            if cnt > peak_count:
                peak_count = cnt
                peak_center = c
            if cnt > 0:
                self.log(f"  {c:10.2f} | {cnt:6d} | {frac:6.3f} | {bar}")

        self.log(f"\n  Peak at |u| = {peak_center:.2f} "
                 f"({peak_count}/{total} = {peak_count/total:.1%})")

        # Store for later tests
        self._all_radii = all_radii
        self._peak_center = peak_center
        self.check("Zero histogram computed", True)

    # -- Test 2: Dominant radius ----------------------------------

    def test2_dominant_radius(self):
        """Find the dominant radius more precisely using KDE."""
        self.log("\n=== Test 2: Dominant radius (precise) ===")

        radii = self._all_radii
        # Filter to reasonable range
        radii_filt = radii[(radii > 0.1) & (radii < 10)]

        # Use log-radius for better resolution
        log_r = np.log(radii_filt)

        # Simple binning in log-space
        bins = np.linspace(np.log(0.1), np.log(10), 100)
        counts, edges = np.histogram(log_r, bins=bins)
        centers = (edges[:-1] + edges[1:]) / 2

        # Find peak
        peak_idx = np.argmax(counts)
        r_peak = np.exp(centers[peak_idx])

        # Also compute median and modes
        r_median = np.median(radii_filt)
        r_mean = np.mean(radii_filt)

        self.log(f"  Peak (log-space):  |u| = {r_peak:.4f}")
        self.log(f"  Median:            |u| = {r_median:.4f}")
        self.log(f"  Mean:              |u| = {r_mean:.4f}")

        # Check specific DRLT candidates
        candidates = {
            '1/sqrt(d-1)=1/2': 1/np.sqrt(D-1),
            '1/sqrt(d)=1/sqrt(5)': 1/np.sqrt(D),
            '1/d=1/5': 1/D,
            '1/sqrt(d^2-1)=1/sqrt(24)': 1/np.sqrt(D**2-1),
            '1/(d-1)=1/4': 1/(D-1),
            'alpha_GUT^(1/2)': np.sqrt(6/(25*np.pi**2)),
        }

        self.log(f"\n  DRLT candidate check:")
        self.log(f"  {'candidate':>30} | {'value':>8} | "
                 f"{'|peak-val|':>10}")
        self.log(f"  {'-'*30}-+-{'-'*8}-+-{'-'*10}")
        for name, val in candidates.items():
            diff = abs(r_peak - val)
            marker = " <--" if diff < 0.15 else ""
            self.log(f"  {name:>30} | {val:8.4f} | "
                     f"{diff:10.4f}{marker}")

        self._r_peak = r_peak
        self.check("Dominant radius identified", True)

    # -- Test 3: DRLT constant matching ---------------------------

    def test3_drlt_constants(self):
        """Test whether the critical circle relates to known constants."""
        self.log("\n=== Test 3: DRLT constant matching ===")

        r = self._r_peak
        self.log(f"  Dominant radius: {r:.4f}")
        self.log(f"\n  Derived quantities:")
        self.log(f"  1/r   = {1/r:.4f}")
        self.log(f"  r^2   = {r**2:.4f}")
        self.log(f"  1/r^2 = {1/r**2:.4f}")
        self.log(f"  log(1/r) = {np.log(1/r):.4f}")

        # Key DRLT constants for comparison
        self.log(f"\n  DRLT constants:")
        self.log(f"  d = {D}")
        self.log(f"  d-1 = {D-1}")
        self.log(f"  d^2-1 = {D**2-1}")
        self.log(f"  1/alpha_GUT = {25*np.pi**2/6:.2f}")

        # The spectral radius of B determines the natural scale
        N = 8
        spec_radii = []
        for t in range(50):
            G = self._make_gram(N, seed=t)
            B, _ = self._edge_adjacency(G)
            spec_radii.append(np.max(np.abs(np.linalg.eigvals(B))))

        rho = np.mean(spec_radii)
        self.log(f"\n  Mean spectral radius rho(B) = {rho:.4f}")
        self.log(f"  1/rho = {1/rho:.4f}")
        self.log(f"  1/sqrt(rho) = {1/np.sqrt(rho):.4f}")
        self.log(f"\n  If Ramanujan: critical circle at 1/sqrt(rho)")
        self.log(f"  Ratio peak / (1/sqrt(rho)) = "
                 f"{r / (1/np.sqrt(rho)):.4f}")

        self.check("DRLT constants compared", True)

    # -- Test 4: N dependence -------------------------------------

    def test4_N_dependence(self):
        """How does the critical circle change with N?"""
        self.log("\n=== Test 4: N dependence ===")

        N_values = [6, 7, 8, 9, 10, 12]
        n_trials = 30

        self.log(f"\n  {'N':>4} | {'median |u|':>11} | {'rho(B)':>8} | "
                 f"{'1/sqrt(rho)':>12} | {'ratio':>6}")
        self.log(f"  {'-'*4}-+-{'-'*11}-+-{'-'*8}-+-{'-'*12}-+-{'-'*6}")

        for N in N_values:
            all_radii = []
            spec_radii = []
            for t in range(n_trials):
                G = self._make_gram(N, seed=t)
                zeros = self._get_zeros(G)
                all_radii.extend(np.abs(zeros))

                B, _ = self._edge_adjacency(G)
                spec_radii.append(np.max(np.abs(np.linalg.eigvals(B))))

            med = np.median(all_radii)
            rho = np.mean(spec_radii)
            r_crit = 1 / np.sqrt(rho)
            ratio = med / r_crit

            self.log(f"  {N:4d} | {med:11.4f} | {rho:8.3f} | "
                     f"{r_crit:12.4f} | {ratio:6.3f}")

        self.log(f"\n  If ratio is constant across N -> "
                 f"critical circle = 1/sqrt(rho(B))")
        self.check("N dependence measured", True)


if __name__ == "__main__":
    CriticalCircle().execute()
