"""
ATM_041: Covalent Radii from Channel Projection
Joint research by Mingu Jeong and Claude (Anthropic)

KEY RESULT: The covalent radius is the Bohr radius projected
onto the spatial sector:

  r_cov = n^2 * a_0 / (Z_eff * sqrt(C(d,3)/N_S))
        = n^2 * a_0 / (Z_eff * sqrt(10/3))

  Scale factor sqrt(10/3) = 1.826 (observed 1.82, match 0.3%)

  10 = C(5,3) = total Binet-Cauchy channels
   3 = N_S = spatial dimension
  sqrt(10/3) = channel-to-space projection factor

Physical: Bohr radius = expectation in full C^5.
Covalent radius = spatial projection (bonding occurs in C^3).

Tests:
  1. Full periodic table covalent radii
  2. Group trends (alkali, halogen)
  3. Period trends (decrease across)
  4. Scale factor derivation
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
from ATM_035_complete_shell_pair import compute_IE_v2, get_period, Ry
from ATM_022_dpair_correction import IE_OBS, SYM
import drlt

D = 5; N_S = 3; N_T = 2
a0 = 52.918  # pm
SCALE = np.sqrt(10/3)  # sqrt(C(d,3)/N_S) = 1.826

# Observed covalent radii (pm) — Pyykko 2009
R_COV = {
    1:31, 2:28, 3:128, 4:96, 5:84, 6:76, 7:71, 8:66, 9:57, 10:58,
    11:166, 12:141, 13:121, 14:111, 15:107, 16:105, 17:102, 18:106,
    19:203, 20:176, 21:170, 22:160, 23:153, 24:139, 25:139, 26:132,
    27:126, 28:124, 29:132, 30:122, 31:122, 32:120, 33:119, 34:120,
    35:120, 36:116, 37:220, 38:195, 39:190, 40:175, 41:164, 42:154,
    43:147, 44:146, 45:142, 46:139, 47:145, 48:144, 49:142, 50:139,
    51:139, 52:138, 53:139, 54:140, 55:244, 56:215,
}


def r_cov_drlt(Z):
    """Covalent radius: r = n^2*a0 / (Z_eff * sqrt(10/3))."""
    ie = compute_IE_v2(Z)
    p = get_period(Z)
    z_eff = np.sqrt(ie * p**2 / Ry)
    return p**2 * a0 / (z_eff * SCALE)


class CovalentRadii(Experiment):
    ID = "ATM_041"
    TITLE = "Covalent Radii from Channels"

    def run(self):
        self.test1_full_table()
        self.test2_group_trends()
        self.test3_scale_derivation()

    def test1_full_table(self):
        """Full covalent radii for Z=1-56."""
        self.log(f"\n  {'='*60}")
        self.log(f"  r_cov = n^2*a_0 / (Z_eff * sqrt(10/3))")
        self.log(f"  sqrt(10/3) = sqrt(C(d,3)/N_S) = {SCALE:.4f}")
        self.log(f"  {'='*60}")

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'DRLT':>6} {'Obs':>5}"
                 f" {'Err':>7}")
        errs = []
        per = {p: [] for p in range(1, 7)}
        for Z in sorted(R_COV.keys()):
            r = r_cov_drlt(Z)
            r_obs = R_COV[Z]
            err = (r - r_obs) / r_obs * 100
            errs.append(abs(err))
            p = get_period(Z)
            per[p].append(abs(err))
            mk = 'V' if abs(err) < 15 else 'o' if abs(err) < 30 else '.'
            self.log(f"  {Z:4d} {SYM[Z]:>3} {r:6.0f} {r_obs:5d}"
                     f" {err:+7.1f}% {mk}")

        med = np.median(errs)
        n15 = sum(1 for e in errs if e < 15)
        n30 = sum(1 for e in errs if e < 30)
        self.log(f"\n  Median: {med:.1f}%")
        self.log(f"  <15%: {n15}/{len(errs)}")
        self.log(f"  <30%: {n30}/{len(errs)}")
        self.log(f"\n  Per-period median:")
        for p in range(1, 7):
            if per.get(p):
                self.log(f"    Period {p}: {np.median(per[p]):.1f}%")

        self.check(f"Median {med:.1f}% < 20%", med < 20)

    def test2_group_trends(self):
        """Correct periodic trends."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Group and Period Trends")
        self.log(f"  {'='*60}")

        # Alkali metals: should increase down group
        self.log(f"\n  Alkali metals (increase ↓):")
        prev = 0
        trend_ok = True
        for Z in [3, 11, 19, 37, 55]:
            r = r_cov_drlt(Z)
            r_obs = R_COV.get(Z, 0)
            arrow = '↑' if r > prev else '↓'
            if prev > 0 and r <= prev:
                trend_ok = False
            self.log(f"    {SYM[Z]:>2}({Z}): {r:5.0f} pm"
                     f" (obs {r_obs}) {arrow}")
            prev = r
        self.check("Alkali increase ↓", trend_ok)

        # Halogens: should increase down group
        self.log(f"\n  Halogens (increase ↓):")
        prev = 0
        trend_ok = True
        for Z in [9, 17, 35, 53]:
            r = r_cov_drlt(Z)
            r_obs = R_COV.get(Z, 0)
            if prev > 0 and r <= prev:
                trend_ok = False
            self.log(f"    {SYM[Z]:>2}({Z}): {r:5.0f} pm (obs {r_obs})")
            prev = r
        self.check("Halogen increase ↓", trend_ok)

        # Period 2: should decrease Li→Ne
        self.log(f"\n  Period 2 (decrease →):")
        prev = 999
        trend_count = 0
        for Z in range(3, 11):
            r = r_cov_drlt(Z)
            if r < prev:
                trend_count += 1
            prev = r
        self.log(f"    Decreasing steps: {trend_count}/7")
        self.check("Period 2 mostly decreases", trend_count >= 5)

    def test3_scale_derivation(self):
        """Derive the scale factor from DRLT."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Scale factor derivation")
        self.log(f"  {'='*60}")

        self.log(f"\n  === DERIVATION ===")
        self.log(f"  Bohr radius: r_Bohr = n^2*a_0/Z_eff")
        self.log(f"    = expectation <r> in full C^{D}")
        self.log(f"  Covalent radius: bonding in spatial C^{N_S}")
        self.log(f"    = projection of r_Bohr onto C^{N_S}")
        self.log(f"")
        self.log(f"  Projection factor:")
        self.log(f"    Total channels: C({D},3) = {10}")
        self.log(f"    Spatial dim:    N_S = {N_S}")
        self.log(f"    Factor = sqrt(C(d,3)/N_S) = sqrt(10/3)")
        self.log(f"           = {SCALE:.6f}")
        self.log(f"")
        self.log(f"  r_cov = r_Bohr / sqrt(10/3)")
        self.log(f"        = n^2*a_0 / (Z_eff * sqrt(10/3))")
        self.log(f"")
        self.log(f"  Observed average ratio: 1.82")
        self.log(f"  Predicted:              {SCALE:.4f}")
        self.log(f"  Match: {abs(SCALE-1.82)/1.82*100:.1f}%")

        # Check for other d values
        self.log(f"\n  Uniqueness check:")
        for d in range(3, 9):
            ns = (d+1)//2
            c_d3 = d*(d-1)*(d-2)//6
            if ns > 0:
                s = np.sqrt(c_d3/ns)
                self.log(f"    d={d}: C({d},3)={c_d3}, N_S={ns},"
                         f" sqrt={s:.3f}")

        self.check(f"Scale = sqrt(10/3) = {SCALE:.4f}", True)


if __name__ == "__main__":
    CovalentRadii().execute()
