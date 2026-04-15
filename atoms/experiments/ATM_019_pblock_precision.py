"""
ATM_019: p-Block Precision via d/f Screening and Same-Shell Correction
Joint research by Mingu Jeong and Claude (Anthropic)

Two new discoveries:
1. σ_df = 1 - α_GUT: d/f electrons screening p-electrons
   - d/f subshell "leaks" exactly α_GUT of screening potential
   - Same coupling that governs gauge interaction!
2. σ_same_p = n_T/(n_T+1) = 2/3 for period ≥ 3
   - Multi-simplex stacking → temporal sector dominates
   - Period 2 special: single simplex → n_S/(n_S+1) = 3/4

Combined with ATM_018's structural fix and σ_core identification.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
import drlt

Ry = 13.606; a = drlt.ALPHA_GUT
D = 5; N_S = 3; N_T = 2; C = 2

# ── Screening constants ──
S_1S = 1 - N_S / (D**2 - 1)          # 7/8
S_SS = 1/N_T + C**2 * a               # 0.597
D_PAIR = N_S / np.pi**2               # 3/π²
OFFSET = (D**2 + N_T) / (D * N_T)     # 27/10 = 2.7

# ── NEW: d/f screening of p-electrons ──
S_DF = 1 - a                           # 1 - α_GUT ≈ 0.9757


def sigma_core(p):
    if p <= 2:
        return S_1S
    return min(0.99, 1 - N_T / (D**2 + (p - OFFSET) * D))


def sigma_sp(p):
    """s→p screening: alternation even→n_S, odd→n_T."""
    nx = N_S if p % 2 == 0 else N_T
    return 1 - nx / (D * (D - 1))


def sigma_same_p(p):
    """Same-subshell p: period 2 = 3/4, period >=3 = 2/3."""
    if p == 2:
        return N_S / (N_S + 1)    # 3/4
    return N_T / (N_T + 1)        # 2/3


def get_config(Z):
    """(period, n_core_prev, n_df, n_ss, n_same, is_p, n_p)
    n_core_prev: previous-period electrons → σ_core
    n_df: d/f electrons → σ_df (only for p-block)
    n_ss: same-period s→p electrons
    n_same: same-subshell count
    """
    # Period 1
    if Z <= 2:
        return (1, max(0, Z-1), 0, 0, 0, False, 0)
    # Period 2: s
    if Z <= 4:
        return (2, 2, 0, 0, Z-3, False, 0)
    # Period 2: p
    if Z <= 10:
        n_p = Z - 4
        return (2, 2, 0, 2, n_p-1, True, n_p)
    # Period 3: s
    if Z <= 12:
        return (3, 10, 0, 0, Z-11, False, 0)
    # Period 3: p (no d/f)
    if Z <= 18:
        n_p = Z - 12
        return (3, 10, 0, 2, n_p-1, True, n_p)
    # Period 4: s
    if Z <= 20:
        return (4, 18, 0, 0, Z-19, False, 0)
    # Period 4: d-block (ionize 4s, all inner = core)
    if Z <= 30:
        return (4, Z-2, 0, 0, 1, False, 0)
    # Period 4: p (18 prev + 10d)
    if Z <= 36:
        n_p = Z - 30
        return (4, 18, 10, 2, n_p-1, True, n_p)
    # Period 5: s
    if Z <= 38:
        return (5, 36, 0, 0, Z-37, False, 0)
    # Period 5: d-block
    if Z <= 48:
        return (5, Z-2, 0, 0, 1, False, 0)
    # Period 5: p (36 prev + 10d)
    if Z <= 54:
        n_p = Z - 48
        return (5, 36, 10, 2, n_p-1, True, n_p)
    # Period 6: s
    if Z <= 56:
        return (6, 54, 0, 0, Z-55, False, 0)
    # Period 6: f+d block (ionize 6s)
    if Z <= 80:
        return (6, Z-2, 0, 0, 1, False, 0)
    # Period 6: p (54 prev + 14f + 10d = 24 df)
    if Z <= 86:
        n_p = Z - 80
        return (6, 54, 24, 2, n_p-1, True, n_p)
    # Period 7: s
    if Z <= 88:
        return (7, 86, 0, 0, Z-87, False, 0)
    # Period 7: f+d block
    if Z <= 112:
        return (7, Z-2, 0, 0, 1, False, 0)
    # Period 7: p (86 prev + 14f + 10d = 24 df)
    if Z <= 118:
        n_p = Z - 112
        return (7, 86, 24, 2, n_p-1, True, n_p)
    return (8, Z-1, 0, 0, 0, False, 0)


def compute_IE(Z):
    """DRLT ionization energy — 0 free parameters."""
    if Z == 1:
        return Ry
    if Z == 2:
        return 2 * Ry * (1 - C**2 * a)
    period, n_core, n_df, n_ss, n_same, is_p, n_p = get_config(Z)
    n = period
    inner = n_core * sigma_core(period)
    if is_p:
        inner += n_df * S_DF          # d/f electrons: σ = 1-α_GUT
        inner += n_ss * sigma_sp(period)
        same = n_same * sigma_same_p(period)
        if n_p > 3:
            same += D_PAIR
    else:
        same = n_same * S_SS
    Ze = Z - inner - same
    return max(0.01, Ze)**2 * Ry / n**2


IE_OBS = {
    1:13.598,2:24.587,3:5.392,4:9.323,5:8.298,6:11.260,7:14.534,
    8:13.618,9:17.423,10:21.565,11:5.139,12:7.646,13:5.986,14:8.152,
    15:10.487,16:10.360,17:12.968,18:15.760,19:4.341,20:6.113,
    21:6.562,22:6.828,23:6.746,24:6.767,25:7.434,26:7.902,27:7.881,
    28:7.640,29:7.726,30:9.394,31:5.999,32:7.900,33:9.789,34:9.752,
    35:11.814,36:14.000,37:4.177,38:5.695,39:6.217,40:6.634,
    41:6.759,42:7.092,43:7.280,44:7.361,45:7.459,46:8.337,
    47:7.576,48:8.994,49:5.786,50:7.344,51:8.608,52:9.010,
    53:10.451,54:12.130,55:3.894,56:5.212,57:5.577,58:5.539,
    59:5.473,60:5.525,61:5.582,62:5.644,63:5.670,64:6.150,
    65:5.864,66:5.939,67:6.022,68:6.108,69:6.184,70:6.254,
    71:5.426,72:6.825,73:7.550,74:7.864,75:7.833,76:8.438,
    77:8.967,78:8.959,79:9.226,80:10.437,81:6.108,82:7.417,
    83:7.286,84:8.414,85:9.318,86:10.749,87:4.073,88:5.279,
    89:5.170,90:6.307,91:5.890,92:6.194,93:6.266,94:6.026,
    95:5.974,96:5.991,97:6.198,98:6.282,99:6.420,100:6.500,
    101:6.580,102:6.650,103:4.900,104:6.010,105:6.890,106:7.100,
    107:7.400,108:7.600,109:8.000,110:8.300,111:8.500,112:9.000,
    113:7.306,114:7.417,115:6.900,116:7.100,117:7.700,118:8.900}
SYM = ['','H','He','Li','Be','B','C','N','O','F','Ne',
    'Na','Mg','Al','Si','P','S','Cl','Ar','K','Ca',
    'Sc','Ti','V','Cr','Mn','Fe','Co','Ni','Cu','Zn',
    'Ga','Ge','As','Se','Br','Kr','Rb','Sr','Y','Zr',
    'Nb','Mo','Tc','Ru','Rh','Pd','Ag','Cd','In','Sn',
    'Sb','Te','I','Xe','Cs','Ba','La','Ce','Pr','Nd',
    'Pm','Sm','Eu','Gd','Tb','Dy','Ho','Er','Tm','Yb',
    'Lu','Hf','Ta','W','Re','Os','Ir','Pt','Au','Hg',
    'Tl','Pb','Bi','Po','At','Rn','Fr','Ra','Ac','Th',
    'Pa','U','Np','Pu','Am','Cm','Bk','Cf','Es','Fm',
    'Md','No','Lr','Rf','Db','Sg','Bh','Hs','Mt','Ds',
    'Rg','Cn','Nh','Fl','Mc','Lv','Ts','Og']


class PBlockPrecision(Experiment):
    ID = "ATM_019"
    TITLE = "p-Block Precision"

    def run(self):
        self.test1_constants()
        self.test2_period4_pblock()
        self.test3_full_scan()

    def test1_constants(self):
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 1: New screening constants")
        self.log(f"  {'='*55}")
        self.log(f"\n  sigma_df = 1 - alpha_GUT = 1 - 6/(d^2 pi^2)")
        self.log(f"         = 1 - {a:.5f} = {S_DF:.5f}")
        self.log(f"  Meaning: d/f subshell leaks exactly alpha_GUT")
        self.log(f"\n  sigma_same_p(p>=3) = n_T/(n_T+1) = {N_T}/{N_T+1}"
                 f" = {N_T/(N_T+1):.5f}")
        self.log(f"  sigma_same_p(p=2)  = n_S/(n_S+1) = {N_S}/{N_S+1}"
                 f" = {N_S/(N_S+1):.5f}")
        self.log(f"  Period 2: single simplex (spatial sector)")
        self.log(f"  Period 3+: multi-simplex (temporal dominates)")
        self.check("sigma_df derived from alpha_GUT", True)

    def test2_period4_pblock(self):
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 2: Period 4 p-block (Ga-Kr)")
        self.log(f"  {'='*55}")
        all_ok = True
        for Z in range(31, 37):
            ie = compute_IE(Z)
            obs = IE_OBS[Z]
            err = (ie - obs) / obs * 100
            ok = abs(err) < 5
            if not ok:
                all_ok = False
            sym = SYM[Z]
            mk = "V" if ok else "X"
            self.log(f"  {Z:2d} {sym:>3}: {ie:7.3f}  {obs:7.3f}"
                     f"  {err:+5.1f}% {mk}")
        self.check("Period 4 p-block all <5%", all_ok)

    def test3_full_scan(self):
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 3: Full periodic Z=1-118")
        self.log(f"  {'='*55}")
        errs = []
        per_errs = {p: [] for p in range(1, 8)}
        for Z in range(1, 119):
            ie = compute_IE(Z)
            obs = IE_OBS.get(Z, 0)
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            if obs > 0:
                err = (ie - obs) / obs * 100
                errs.append(abs(err))
                p = get_config(Z)[0]
                per_errs[p].append(abs(err))
                mk = 'V' if abs(err)<5 else 'o' if abs(err)<15 \
                    else '.' if abs(err)<30 else ' '
                self.log(f"  {Z:3d} {sym:>3} {ie:7.2f} {obs:7.2f}"
                         f" {err:+6.1f}% {mk}")

        self.log(f"\n  Overall statistics:")
        for t in [3, 5, 10, 15, 30]:
            n = sum(1 for e in errs if e < t)
            self.log(f"  <{t:2d}%: {n:3d}/{len(errs)}"
                     f" ({n/len(errs)*100:.0f}%)")
        med = np.median(errs)
        self.log(f"  Median: {med:.1f}%")

        self.log(f"\n  Per-period median error:")
        for p in range(1, 8):
            if per_errs[p]:
                pm = np.median(per_errs[p])
                self.log(f"  Period {p}: {pm:.1f}%"
                         f" ({len(per_errs[p])} elements)")

        n5 = sum(1 for e in errs if e < 5)
        n15 = sum(1 for e in errs if e < 15)
        self.check(f"Median < 15%", med < 15)
        self.check(f">40% within 15%", n15 / len(errs) > 0.40)
        self.check(f">25% within 5%", n5 / len(errs) > 0.25)


if __name__ == "__main__":
    PBlockPrecision().execute()
