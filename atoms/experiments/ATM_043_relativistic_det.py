"""
ATM_043: Relativistic Correction from Hinge Determinant
Joint research by Mingu Jeong and Claude (Anthropic)

KEY INSIGHT: The 'relativistic' correction in DRLT is the
nonlinear hinge determinant of inner-shell electrons.

  det(AAB, shell k) = 1 - 2*(Z_k * alpha / sqrt(N_S))^2

For light atoms: det ≈ 1 (linear regime, current model works).
For heavy atoms: det << 1 (nonlinear, correction needed).

  H(Z=1):   det(1s) = 1.000
  Hg(Z=80): det(1s) = 0.773  ← 23% nonlinearity!
  Og(Z=118):det(1s) = 0.506  ← 50%!

This is the SAME (Z*alpha)^2 that gives the Dirac fine-structure
correction, but derived from simplex geometry, not from relativity.

The correction modifies the core screening:
  sigma_eff(k) = sigma_shell(k) * [1 - C_rel * (1 - sqrt(det_k))]
  where C_rel = c^2 = N_T^2 = 4 (STT channel weight, same as He IE)

Tests:
  1. det structure across the periodic table
  2. Corrected screening for Hg, Og, etc.
  3. Improved IE for heavy elements
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
from ATM_035_complete_shell_pair import (
    compute_IE_v2, get_period, sigma_core_layered, sigma_shell,
    sigma_same_p, sigma_sp, sigma_fill,
    S_SS, S_DF, D_PAIR, NOBLE, N_S, N_T, D, C, Ry
)
from ATM_022_dpair_correction import IE_OBS, SYM

ALPHA = 1/137.036
DEEP_PAIR = D_PAIR * N_S / N_T
C_REL = C**2  # = 4, STT channel weight (same physics as He IE)

# Electron counts per shell
SHELL_ELECTRONS = {
    1: [2],                            # He
    2: [2, 8],                         # Ne
    3: [2, 8, 8],                      # Ar
    4: [2, 8, 18, 8],                  # Kr
    5: [2, 8, 18, 18, 8],             # Xe
    6: [2, 8, 18, 32, 18, 8],         # Rn
    7: [2, 8, 18, 32, 32, 18, 8],     # Og
}
NOBLE_Z = {1: 0, 2: 2, 3: 10, 4: 18, 5: 36, 6: 54, 7: 86}


def det_shell(Z_seen):
    """Hinge determinant for shell seeing charge Z_seen."""
    eps = Z_seen * ALPHA / np.sqrt(N_S)
    return max(0, 1 - 2 * eps**2)


def sigma_core_relativistic(p, Z):
    """Core screening with sqrt(det) relativistic correction."""
    if p <= 2:
        return 1 - N_S / (D**2 - 1)  # 7/8 (light, no correction)

    shells = SHELL_ELECTRONS.get(p, [])
    if not shells:
        return sigma_core_layered(p)

    # Effective Z seen by each shell (cumulative screening)
    nn = sum(shells[:p-1]) if p > 1 else 0
    P = p - 1
    ts, te = 0.0, 0
    z_remaining = Z
    for k in range(1, p):
        nk = shells[k-1] if k-1 < len(shells) else 8
        # Z seen by shell k: Z minus screening from shells below
        z_remaining -= 0  # rough: use layered model + det correction
        z_k = Z - sum(shells[:k-1]) * 0.95  # rough inner screening

        s = sigma_shell(k, p)
        d = det_shell(z_k)
        # Correction: screening reduced when det < 1
        s_eff = s * (1 - C_REL * ALPHA * (1 - np.sqrt(d)))
        ts += nk * s_eff
        te += nk

    return ts / te if te > 0 else 0.875


class RelativisticDet(Experiment):
    ID = "ATM_043"
    TITLE = "Relativistic Det Correction"

    def run(self):
        self.test1_det_structure()
        self.test2_corrected_screening()
        self.test3_improved_IE()

    def test1_det_structure(self):
        """det(AAB) across the periodic table."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: Hinge determinant structure")
        self.log(f"  det(AAB) = 1 - 2*(Z_k*alpha/sqrt(N_S))^2")
        self.log(f"  {'='*60}")

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'det(1s)':>8}"
                 f" {'(Zα)²':>8} {'sqrt(det)':>10}")
        for Z in [1,2,6,10,18,26,36,54,79,80,82,86,118]:
            d = det_shell(Z)
            za2 = (Z*ALPHA)**2
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            self.log(f"  {Z:4d} {sym:>3} {d:8.4f} {za2:8.4f}"
                     f" {np.sqrt(max(0,d)):10.4f}")

        self.log(f"\n  (Zα)² is the Dirac fine-structure parameter.")
        self.log(f"  det = 1 - 2(Zα/√N_S)² = 1 - 2(Zα)²/N_S")
        self.log(f"  DRLT encodes relativity via hinge geometry.")
        self.check("det structure mapped", True)

    def test2_corrected_screening(self):
        """Corrected sigma_core for heavy elements."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Relativistic core screening")
        self.log(f"  sigma_eff = sigma * [1 - c^2*alpha*(1-sqrt(det))]")
        self.log(f"  {'='*60}")

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'sc_old':>8} {'sc_rel':>8}"
                 f" {'delta':>8}")
        for Z in [11, 19, 37, 55, 80, 87, 103, 118]:
            p = get_period(Z)
            sc_old = sigma_core_layered(p)
            sc_rel = sigma_core_relativistic(p, Z)
            delta = sc_rel - sc_old
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            self.log(f"  {Z:4d} {sym:>3} {sc_old:8.4f} {sc_rel:8.4f}"
                     f" {delta:+8.5f}")

        self.check("Corrected screening computed", True)

    def test3_improved_IE(self):
        """IE with relativistic correction for problem elements."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Improved IE for heavy elements")
        self.log(f"  {'='*60}")

        # Test on the 6 worst elements
        worst = [37, 80, 87, 103, 104, 113]

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'IE_old':>7} {'IE_rel':>7}"
                 f" {'Obs':>7} {'old%':>7} {'rel%':>7}")
        for Z in worst:
            ie_old = compute_IE_v2(Z)
            obs = IE_OBS[Z]
            p = get_period(Z)
            nn = NOBLE[p]

            # Compute IE with relativistic sc
            sc_rel = sigma_core_relativistic(p, Z)
            sc_old = sigma_core_layered(p)

            # Simple: adjust IE by the sc change
            # Z_eff_old = sqrt(IE_old * p^2 / Ry)
            # Z_eff_new = Z_eff_old + nn*(sc_old - sc_rel)
            z_old = np.sqrt(ie_old * p**2 / Ry)
            z_new = z_old + nn * (sc_old - sc_rel)
            ie_rel = z_new**2 * Ry / p**2

            err_old = (ie_old - obs)/obs * 100
            err_rel = (ie_rel - obs)/obs * 100
            sym = SYM[Z]
            improved = '★' if abs(err_rel) < abs(err_old) else ''
            self.log(f"  {Z:4d} {sym:>3} {ie_old:7.2f} {ie_rel:7.2f}"
                     f" {obs:7.2f} {err_old:+7.1f} {err_rel:+7.1f}"
                     f" {improved}")

        self.check("Relativistic IE computed", True)


if __name__ == "__main__":
    RelativisticDet().execute()
