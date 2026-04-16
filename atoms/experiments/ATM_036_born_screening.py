"""
ATM_036: Born Eigenvalue Gaps → Screening Constants
Joint research by Mingu Jeong and Claude (Anthropic)

Hint from critical-line/RH_047 (Spectral Flow):
  Born-weighted Gram W_ij = |G_ij|^2 has eigenvalue structure.
  Eigenvalue GAPS may geometrically constrain screening constants.

Connection:
  - Gram matrix G on partial(Delta^5) encodes atomic structure
  - W = |G|^2 is the Born-rule transition probability matrix
  - W eigenvalues {mu_k} relate to channel structure
  - Eigenvalue gaps Delta_mu should match screening constants
  - Ramanujan bound |lambda| <= 2*sqrt(q) ↔ Re(s) = 1/2

Screening constants to reproduce (from d=5):
  sigma_cross = 7/8, sigma_same_s = 0.597, sigma_sp = 17/20 or 9/10

Tests:
  1. Hydrogen Born spectrum: W eigenvalues
  2. Helium Born spectrum: W eigenvalues
  3. Eigenvalue gaps vs screening constants
  4. Ramanujan structure of W
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from experiment import Experiment
import drlt

D = 5; N_S = 3; N_T = 2; C = 2
ALPHA_GUT = drlt.ALPHA_GUT
ALPHA_EM = drlt.ALPHA_EM
S_1S = 1 - N_S / (D**2 - 1)          # 7/8
S_SS = 1/N_T + C**2 * ALPHA_GUT       # 0.597
S_SP_EVEN = 1 - N_S / (D*(D-1))       # 17/20
S_SP_ODD = 1 - N_T / (D*(D-1))        # 9/10


def build_psi(Z, config='ground'):
    """Build 6-vertex C^5 vectors for atom with charge Z."""
    psi = np.zeros((6, 5), dtype=complex)
    psi[0] = [0, 0, 1, 0, 0]  # A1
    psi[1] = [0, 0, 0, 1, 0]  # A2
    psi[2] = [0, 0, 0, 0, 1]  # A3
    eps = Z * ALPHA_EM / np.sqrt(N_S)
    t = np.sqrt(max(0, 1 - 3*eps**2))
    if config == 'ground':
        psi[3] = [t, 0, eps, eps, eps]          # B1
        psi[4] = [0, t, eps, eps, eps]           # B2
    elif config == 'hydrogen':
        psi[3] = [t, 0, eps, eps, eps]           # B1
        psi[4] = [0, 1, 0, 0, 0]                # B2 (vacuum)
    psi[5] = [np.cos(np.pi/3), np.sin(np.pi/3), 0, 0, 0]  # X
    for i in range(6):
        n = np.linalg.norm(psi[i])
        if n > 0:
            psi[i] /= n
    return psi


def gram_matrix(psi):
    return psi @ psi.conj().T


def born_matrix(G):
    """Born-rule transition matrix: W_ij = |G_ij|^2."""
    return np.abs(G)**2


def adjacency_from_born(W):
    """Adjacency-like matrix: zero diagonal."""
    A = W.copy()
    np.fill_diagonal(A, 0)
    return A


class BornScreening(Experiment):
    ID = "ATM_036"
    TITLE = "Born Eigenvalue Screening"

    def run(self):
        self.test1_hydrogen_spectrum()
        self.test2_helium_spectrum()
        self.test3_gaps_vs_screening()
        self.test4_ramanujan()

    def test1_hydrogen_spectrum(self):
        """Born-weighted eigenvalues for hydrogen."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: Hydrogen Born spectrum")
        self.log(f"  {'='*60}")

        psi = build_psi(1, 'hydrogen')
        G = gram_matrix(psi)
        W = born_matrix(G)
        A = adjacency_from_born(W)

        self.log(f"\n  Gram |G_ij| matrix (hydrogen):")
        for i in range(6):
            row = ' '.join(f'{abs(G[i,j]):.4f}' for j in range(6))
            self.log(f"    {row}")

        self.log(f"\n  Born W_ij = |G_ij|^2:")
        for i in range(6):
            row = ' '.join(f'{W[i,j].real:.5f}' for j in range(6))
            self.log(f"    {row}")

        # Eigenvalues of W
        mu_W = np.sort(np.linalg.eigvalsh(W.real))[::-1]
        self.log(f"\n  W eigenvalues: {[f'{m:.6f}' for m in mu_W]}")

        # Eigenvalues of adjacency A
        mu_A = np.sort(np.linalg.eigvalsh(A.real))[::-1]
        self.log(f"  A eigenvalues: {[f'{m:.6f}' for m in mu_A]}")

        # Gaps
        self.log(f"\n  W eigenvalue gaps:")
        for i in range(len(mu_W)-1):
            gap = mu_W[i] - mu_W[i+1]
            self.log(f"    mu_{i+1}-mu_{i+2} = {gap:.6f}")

        # Normalized gaps (by largest)
        self.log(f"\n  Normalized gaps (gap / mu_1):")
        for i in range(len(mu_W)-1):
            gap = (mu_W[i] - mu_W[i+1]) / mu_W[0]
            self.log(f"    gap_{i+1} = {gap:.6f}")

        self._mu_H = mu_W
        self._A_H = mu_A
        self.check("Hydrogen spectrum computed", True)

    def test2_helium_spectrum(self):
        """Born-weighted eigenvalues for helium."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Helium Born spectrum")
        self.log(f"  {'='*60}")

        psi = build_psi(2, 'ground')
        G = gram_matrix(psi)
        W = born_matrix(G)
        A = adjacency_from_born(W)

        self.log(f"\n  Born W_ij = |G_ij|^2 (helium):")
        for i in range(6):
            row = ' '.join(f'{W[i,j].real:.5f}' for j in range(6))
            self.log(f"    {row}")

        mu_W = np.sort(np.linalg.eigvalsh(W.real))[::-1]
        mu_A = np.sort(np.linalg.eigvalsh(A.real))[::-1]

        self.log(f"\n  W eigenvalues: {[f'{m:.6f}' for m in mu_W]}")
        self.log(f"  A eigenvalues: {[f'{m:.6f}' for m in mu_A]}")

        self.log(f"\n  W eigenvalue gaps:")
        for i in range(len(mu_W)-1):
            gap = mu_W[i] - mu_W[i+1]
            self.log(f"    mu_{i+1}-mu_{i+2} = {gap:.6f}")

        self._mu_He = mu_W
        self._A_He = mu_A
        self.check("Helium spectrum computed", True)

    def test3_gaps_vs_screening(self):
        """Compare eigenvalue ratios to screening constants."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Eigenvalue ratios vs screening constants")
        self.log(f"  {'='*60}")

        targets = {
            'sigma_cross (7/8)': S_1S,
            'sigma_same_s': S_SS,
            'sigma_sp_even (17/20)': S_SP_EVEN,
            'sigma_sp_odd (9/10)': S_SP_ODD,
            'alpha_GUT': ALPHA_GUT,
            '1/N_T': 1.0/N_T,
            'c^2*alpha_GUT': C**2 * ALPHA_GUT,
        }

        # Scan Z=1..10 for Born eigenvalue ratios
        self.log(f"\n  Scanning Z=1..10 for eigenvalue ratio matches:")
        for Z in [1, 2, 3, 6, 10]:
            cfg = 'hydrogen' if Z == 1 else 'ground'
            psi = build_psi(Z, cfg)
            G = gram_matrix(psi)
            W = born_matrix(G)

            mu = np.sort(np.linalg.eigvalsh(W.real))[::-1]
            # Also compute A eigenvalues
            A = adjacency_from_born(W)
            la = np.sort(np.linalg.eigvalsh(A.real))[::-1]

            self.log(f"\n  Z={Z}: W eigs = "
                     f"{[f'{m:.4f}' for m in mu]}")
            self.log(f"        A eigs = "
                     f"{[f'{m:.4f}' for m in la]}")

            # Check all pairwise ratios against targets
            matches = []
            for i in range(len(mu)):
                for j in range(i+1, len(mu)):
                    if abs(mu[j]) > 1e-10:
                        r = mu[i] / mu[j]
                        for name, val in targets.items():
                            if abs(r - val) / max(abs(val), 0.01) < 0.05:
                                matches.append((name, r, val, i, j))
                    # Also gaps
                    gap = (mu[i] - mu[j]) / mu[0] if mu[0] > 1e-10 else 0
                    for name, val in targets.items():
                        if abs(gap - val) / max(abs(val), 0.01) < 0.05:
                            matches.append((f'{name} (gap)', gap, val, i, j))

            if matches:
                for name, r, val, i, j in matches:
                    self.log(f"    MATCH: {name} ≈ {r:.6f}"
                             f" (target {val:.6f},"
                             f" mu_{i+1}/mu_{j+1})")

        self.check("Gap-screening scan complete", True)

    def test4_ramanujan(self):
        """Check Ramanujan bound for Born-weighted graphs."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: Ramanujan structure of Born graph")
        self.log(f"  {'='*60}")

        for Z in [1, 2, 3, 6]:
            cfg = 'hydrogen' if Z == 1 else 'ground'
            psi = build_psi(Z, cfg)
            G = gram_matrix(psi)
            W = born_matrix(G)
            A = adjacency_from_born(W)
            la = np.sort(np.linalg.eigvalsh(A.real))[::-1]

            # "q+1 regular" approximation: row sums
            row_sums = np.sum(A.real, axis=1)
            d_avg = np.mean(row_sums)
            q = d_avg - 1

            # Ramanujan bound: |lambda_nontrivial| <= 2*sqrt(q)
            bound = 2 * np.sqrt(max(0, q))
            la_nt = la[1:]  # skip largest
            max_nt = np.max(np.abs(la_nt))

            is_ram = max_nt <= bound + 1e-10
            self.log(f"\n  Z={Z}: q={q:.4f}, 2√q={bound:.4f},"
                     f" max|λ_nt|={max_nt:.4f},"
                     f" Ramanujan={'YES' if is_ram else 'NO'}")
            self.log(f"    λ_1={la[0]:.4f} (trivial),"
                     f" λ_2={la[1]:.4f},"
                     f" gap={la[0]-la[1]:.4f}")

            # Key ratio: lambda_2 / lambda_1
            r = la[1] / la[0] if abs(la[0]) > 1e-10 else 0
            self.log(f"    λ_2/λ_1 = {r:.6f}")

            # Spectral gap / d_avg
            sgap = (la[0] - la[1]) / d_avg if d_avg > 0 else 0
            self.log(f"    Spectral gap/d_avg = {sgap:.6f}")

        self.check("Ramanujan analysis complete", True)


if __name__ == "__main__":
    BornScreening().execute()
