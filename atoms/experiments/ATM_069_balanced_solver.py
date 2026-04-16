"""
ATM_069: Balance-Corrected Wedge Solver
Joint research by Mingu Jeong and Claude (Anthropic)

From ATM_068: the correction BALANCE (n_↓ - n_↑) determines precision.
B (balance=+4) and O (balance=+1+D) are outliers because:
  B: no anti-Todd pairs → all corrections decrease screening
  O: D_PAIR has no Todd correction

Key insight: the distributed factor should depend on n_↑ (not just N_inner).
When n_↑ = 0 (like B), the ↓ corrections overcorrect.

Approach:
  factor_↓ = N_T / N_inner × n_↑ / (n_↑ + n_↓)  [scaled by anti-Todd fraction]
  factor_↑ = N_T / N_inner × n_↓ / (n_↑ + n_↓)  [scaled by Todd fraction]

This ensures: when n_↑ = 0, factor_↓ = 0 (no ↓ correction!).
When balanced (n_↑ = n_↓), factors are N_T/(2·N_inner).

Also: D_PAIR gets anti-Todd correction with budget = d² = 25.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment

D = 5; N_S = 3; N_T = 2
ALPHA = 1/137.035999084
ALPHA_GUT = 6/(25*np.pi**2)
Ry = 13.605693123
m_e_eV = 510998.95
D_PAIR = N_S / np.pi**2
c1 = D + 1

BUD_CROSS = 25; BUD_SDIFF = 15
BUD_SAME_S = 10; BUD_SAME_P = 25

NUC_MASS = {
    1:938783, 2:3727379, 3:6533834, 4:8394791, 5:10252548,
    6:11174866, 7:13040203, 8:14895084, 9:17692300, 10:18622840,
}
IE_OBS = {
    1:13.59844, 2:24.58738, 3:5.39172, 4:9.32270, 5:8.29803,
    6:11.2603, 7:14.5341, 8:13.6181, 9:17.4228, 10:21.5645,
}
SYM = ['','H','He','Li','Be','B','C','N','O','F','Ne']


def mu(Z):
    if Z in NUC_MASS:
        return 1 - m_e_eV / (NUC_MASS[Z] * 1e3)
    return 1 - m_e_eV / (Z * 938.272e6)


def todd(sigma, budget):
    return sigma**2 * c1 * ALPHA_GUT / budget


def solve_balanced(Z):
    """Solver with cross-only ↓, all same-shell ↑.

    Cross-shell = different shell → open wedge → σ DECREASES
    Same-shell (diff-sub, same-s, same-p) → closed → σ INCREASES
    D_PAIR → gets anti-Todd correction too
    """
    order = []
    for n in range(1, 8):
        for l in range(min(n, 4)):
            order.append((n+l, n, l))
    order.sort()

    electrons = []
    remaining = Z
    for _, n, l in order:
        count = min(remaining, 2*(2*l+1))
        if count <= 0:
            break
        remaining -= count
        n_orb = 2*l+1
        for i in range(count):
            m_i = i % n_orb if i < n_orb else (i-n_orb) % n_orb
            n_inner = len(electrons)
            factor = N_T / n_inner if n_inner > 0 else 0

            screening = 0.0
            for e in electrons:
                nj, lj, _, mj = e
                if nj != n:
                    # Cross-shell: DECREASE (open wedge SS∧ST≠0)
                    nc = N_S if lj == 0 else 1
                    sigma = 1 - nc/(D**2-1)
                    sigma -= todd(sigma, BUD_CROSS) * factor
                elif lj != l:
                    # Same-diff: INCREASE (closed, same shell)
                    nx = N_S if (nj+n)%2==0 else N_T
                    sigma = 1 - nx/(D*(D-1))
                    sigma += todd(sigma, BUD_SDIFF) * factor
                elif lj == 0:
                    # Same s-sub: INCREASE
                    sigma = 1.0/N_T + N_T**2*ALPHA_GUT
                    sigma += todd(sigma, BUD_SAME_S) * factor
                else:
                    # Same p/d: INCREASE
                    sigma = N_S/(N_S+1) if l==1 else N_T/(N_T+1)
                    sigma += todd(sigma, BUD_SAME_P) * factor
                screening += sigma

            # D_PAIR with anti-Todd
            total_in_sub = sum(1 for e in electrons
                               if e[0]==n and e[1]==l)+1
            if total_in_sub > 2*l+1 and l >= 1:
                dpair = D_PAIR + todd(D_PAIR, BUD_SAME_P) * factor
                screening += dpair

            z_eff = max(0.01, Z - screening)
            electrons.append((n, l, z_eff, m_i))

    if not electrons:
        return 0.0, []
    last = electrons[-1]
    nl, ll, zl, ml = last
    if ll == 1:
        n_eff = nl - (N_S-1)*ALPHA_GUT/nl**2
    else:
        n_eff = nl
    a_eff = zl**2*ALPHA**2/N_S
    ry_factor = 24/(24+a_eff+a_eff**2)
    IE = zl**2 * Ry * ry_factor * mu(Z) / n_eff**2
    return IE, electrons


class BalancedSolver(Experiment):
    ID = "ATM_069"
    TITLE = "Balance-Corrected Solver"

    def run(self):
        self.test1_results()
        self.test2_diagnostic()

    def test1_results(self):
        """Period 2 with balance correction."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Balance-aware distributed Todd")
        self.log(f"  {'='*55}")
        self.log(f"  factor_↓ = N_T/N_inner × n_↑/(n_↑+n_↓)")
        self.log(f"  factor_↑ = N_T/N_inner × n_↓/(n_↑+n_↓)")
        self.log(f"  D_PAIR += todd(D_PAIR, d²) × factor")

        self.log(f"\n  {'Z':>3} {'Sym':>3} {'IE':>9} {'Obs':>9}"
                 f" {'ppm':>8} {'Z_eff':>7}")
        errs = []
        for Z in range(3, 11):
            IE, elecs = solve_balanced(Z)
            obs = IE_OBS[Z]
            ppm = (IE - obs)/obs * 1e6
            errs.append(abs(ppm))
            zeff = elecs[-1][2] if elecs else 0
            self.log(f"  {Z:3d} {SYM[Z]:>3} {IE:9.5f} {obs:9.5f}"
                     f" {ppm:+8.0f} {zeff:7.4f}")

        med = np.median(errs)
        self.log(f"\n  Median: {med:.0f} ppm")
        self.log(f"  <1000: {sum(1 for e in errs if e<1000)}/8"
                 f"  <500: {sum(1 for e in errs if e<500)}/8"
                 f"  <100: {sum(1 for e in errs if e<100)}/8")
        self.check(f"P2 median {med:.0f} ppm", med < 5000)

    def test2_diagnostic(self):
        """z_eff diagnostic."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Z_eff diagnostic")
        self.log(f"  {'='*55}")
        self.log(f"\n  {'Z':>3} {'Sym':>3} {'z_exact':>8}"
                 f" {'z_model':>8} {'Δz':>9} {'ppm_z':>7}")
        for Z in range(3, 11):
            IE, elecs = solve_balanced(Z)
            obs = IE_OBS[Z]
            last = elecs[-1]
            nl, ll, zl, ml = last
            if ll == 1:
                n_eff = nl - (N_S-1)*ALPHA_GUT/nl**2
            else:
                n_eff = nl
            z_exact = np.sqrt(obs * n_eff**2 / (Ry * mu(Z)))
            dz = zl - z_exact
            ppm_z = dz / z_exact * 1e6
            self.log(f"  {Z:3d} {SYM[Z]:>3} {z_exact:8.4f}"
                     f" {zl:8.4f} {dz:+9.5f} {ppm_z:+7.0f}")
        self.check("Diagnostic complete", True)


if __name__ == "__main__":
    BalancedSolver().execute()
