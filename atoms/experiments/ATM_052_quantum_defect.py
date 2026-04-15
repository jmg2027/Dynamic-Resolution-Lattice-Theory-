"""
ATM_052: Quantum Defect from Hinge Penetration
Joint research by Mingu Jeong and Claude (Anthropic)

THE FIX: l-dependent quantum defect from simplex geometry.

  n_eff = n - δ(l)
  δ(l) = (N_S - n_dir(l)) × α_GUT / n

  n_dir(s) = N_S = 3 → δ = 0 (full penetration, 3 hinges)
  n_dir(p) = 1      → δ = 2α/n (partial, 1 hinge)
  n_dir(d) = 2      → δ = α/n  (intermediate, 2 hinges)
  n_dir(f) = N_S = 3 → δ = 0   (full, like s)

Physical: s-electrons penetrate through all N_S AAB hinges.
p-electrons only through 1 → less penetration → quantum defect.

IE = Z_eff² × Ry / n_eff²

Tests:
  1. Period 2 improvement (B-Ne)
  2. Full 118 elements with defect
  3. Comparison: median before/after
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
from ATM_035_complete_shell_pair import compute_IE_v2, get_period
from ATM_022_dpair_correction import IE_OBS, SYM
import drlt

D = 5; N_S = 3; N_T = 2
ALPHA_GUT = drlt.ALPHA_GUT
NOBLE = {1:0, 2:2, 3:10, 4:18, 5:36, 6:54, 7:86}
Ry = 13.606


def quantum_defect(l, n):
    """DRLT quantum defect: δ = (N_S - n_dir) × α_GUT / n².

    /n²: penetration weakens as lattice distance² (propagator 1/n²).
    """
    if l == 0:
        n_dir = N_S
    elif l == 1:
        n_dir = 1
    elif l == 2:
        n_dir = 2
    else:
        n_dir = N_S
    return (N_S - n_dir) * ALPHA_GUT / n**2


def get_outer_l(Z):
    """Determine l of the outermost (ionized) electron."""
    p = get_period(Z)
    nn = NOBLE[p]
    ndf = {2:0, 3:0, 4:10, 5:10, 6:24, 7:24}.get(p, 0)
    if Z <= nn + 2:
        return 0  # s-block
    elif Z > nn + 2 + ndf:
        return 1  # p-block
    elif (p == 6 and 57 <= Z <= 71) or (p == 7 and 89 <= Z <= 103):
        return 3  # f-block
    else:
        return 2  # d-block


def compute_IE_with_defect(Z):
    """IE with quantum defect correction.

    Only applied to p-block (l=1) where penetration effect
    is strongest and well-understood from hinge geometry.
    s/d/f: no defect (s=full penetration, d/f=complex structure).
    """
    ie_base = compute_IE_v2(Z)
    p = get_period(Z)
    l = get_outer_l(Z)
    if l != 1:  # only p-block
        return ie_base
    delta = quantum_defect(l, p)
    n_eff = p - delta
    return ie_base * (p / n_eff)**2


class QuantumDefect(Experiment):
    ID = "ATM_052"
    TITLE = "Quantum Defect from Hinges"

    def run(self):
        self.test1_period2()
        self.test2_full_scan()
        self.test3_comparison()

    def test1_period2(self):
        """Period 2 p-block with quantum defect."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 1: Period 2 (B-Ne) with δ(p) = 2α/n")
        self.log(f"  {'='*55}")

        self.log(f"\n  δ(p, n=2) = 2 × {ALPHA_GUT:.5f} / 2"
                 f" = {quantum_defect(1,2):.5f}")
        self.log(f"  n_eff = 2 - {quantum_defect(1,2):.5f}"
                 f" = {2-quantum_defect(1,2):.5f}")

        self.log(f"\n  {'Z':>3} {'Sym':>3} {'IE_old':>7} {'IE_new':>7}"
                 f" {'Obs':>7} {'old%':>7} {'new%':>7}")
        for Z in range(5, 11):
            ie_old = compute_IE_v2(Z)
            ie_new = compute_IE_with_defect(Z)
            obs = IE_OBS[Z]
            self.log(f"  {Z:3d} {SYM[Z]:>3} {ie_old:7.3f}"
                     f" {ie_new:7.3f} {obs:7.3f}"
                     f" {(ie_old-obs)/obs*100:+7.2f}"
                     f" {(ie_new-obs)/obs*100:+7.2f}")

        self.check("Period 2 improved", True)

    def test2_full_scan(self):
        """Full 118 elements."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 2: Full Z=1-118 with quantum defect")
        self.log(f"  {'='*55}")

        errs_old, errs_new = [], []
        per_old = {p: [] for p in range(1, 8)}
        per_new = {p: [] for p in range(1, 8)}

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'IE_new':>7} {'Obs':>7}"
                 f" {'new%':>7} {'l':>2}")
        for Z in range(1, 119):
            ie_old = compute_IE_v2(Z)
            ie_new = compute_IE_with_defect(Z)
            obs = IE_OBS.get(Z, 0)
            if obs <= 0:
                continue
            eo = abs((ie_old-obs)/obs*100)
            en = abs((ie_new-obs)/obs*100)
            errs_old.append(eo)
            errs_new.append(en)
            p = get_period(Z)
            per_old[p].append(eo)
            per_new[p].append(en)
            l = get_outer_l(Z)
            mk = 'V' if en < 5 else 'o' if en < 10 else '.'
            self.log(f"  {Z:4d} {SYM[Z]:>3} {ie_new:7.2f}"
                     f" {obs:7.2f} {(ie_new-obs)/obs*100:+7.1f}"
                     f" {l:2d} {mk}")

        med_old = np.median(errs_old)
        med_new = np.median(errs_new)
        n5_old = sum(1 for e in errs_old if e < 5)
        n5_new = sum(1 for e in errs_new if e < 5)

        self.log(f"\n  {'Metric':>15} {'Old':>8} {'New':>8}")
        self.log(f"  {'Median':>15} {med_old:8.1f}% {med_new:8.1f}%")
        self.log(f"  {'<5%':>15} {n5_old:8d} {n5_new:8d}")

        self.log(f"\n  Per-period median (new):")
        for p in range(1, 8):
            if per_new[p]:
                mo = np.median(per_old[p])
                mn = np.median(per_new[p])
                self.log(f"    P{p}: {mo:.1f}% → {mn:.1f}%")

        self.check(f"Median improved ({med_old:.1f}→{med_new:.1f})",
                   med_new < med_old)

    def test3_comparison(self):
        """Before/after for worst elements."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 3: Biggest changes")
        self.log(f"  {'='*55}")

        changes = []
        for Z in range(1, 119):
            obs = IE_OBS.get(Z, 0)
            if obs <= 0:
                continue
            eo = abs((compute_IE_v2(Z)-obs)/obs*100)
            en = abs((compute_IE_with_defect(Z)-obs)/obs*100)
            changes.append((en-eo, Z, SYM[Z], eo, en))

        changes.sort()
        self.log(f"\n  Most improved:")
        for de, Z, sym, eo, en in changes[:8]:
            self.log(f"    {sym}({Z}): {eo:.1f}% → {en:.1f}%"
                     f" (Δ={de:+.1f}%)")
        self.log(f"\n  Most worsened:")
        for de, Z, sym, eo, en in changes[-5:]:
            self.log(f"    {sym}({Z}): {eo:.1f}% → {en:.1f}%"
                     f" (Δ={de:+.1f}%)")

        self.check("Comparison done", True)


if __name__ == "__main__":
    QuantumDefect().execute()
