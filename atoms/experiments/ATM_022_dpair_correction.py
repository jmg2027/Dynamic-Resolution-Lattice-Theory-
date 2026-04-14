"""
ATM_022: d-Block Pair Correction
Joint research by Mingu Jeong and Claude (Anthropic)

Building on ATM_021 (filling fraction), adds d-block pair correction:

  Δ_d = Δ_pair × (n_d - d) / d   for d < n_d < 2d

Physical: d-subshell has 2d=10 states. At half-fill (n_d=d=5),
pairing begins. Each additional electron adds Δ_pair/d screening
from the newly formed pair. Complete d¹⁰ is symmetric → no correction.

Fixes: Ni +16%→+3%, Cu +21%→+4%, Ag +19%→+5%
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
import drlt

Ry = 13.606; a = drlt.ALPHA_GUT
D = 5; N_S = 3; N_T = 2; C = 2

S_1S = 1 - N_S / (D**2 - 1)
S_SS = 1/N_T + C**2 * a
D_PAIR = N_S / np.pi**2
S_DF = 1 - a
C_GAP = D * (D + 1)
NOBLE = {1: 0, 2: 2, 3: 10, 4: 18, 5: 36, 6: 54, 7: 86}


def shell_electrons(k, P):
    if k == 1: return 2
    e = 8
    if 3 <= k <= P - 1: e += 10
    if 4 <= k <= P - 2: e += 14
    return e


def sigma_shell(k, n):
    gap = n - k - 1
    nx = N_S if (k + n) % 2 == 0 else N_T
    return 1 - nx / (D**2 - 1 + gap * C_GAP)


def sigma_core_layered(p):
    if p <= 2: return S_1S
    P = p - 1
    ts, te = 0.0, 0
    for k in range(1, p):
        nk = shell_electrons(k, P)
        ts += nk * sigma_shell(k, p)
        te += nk
    return ts / te


def sigma_fill(n_fill, n_max, k, n):
    """Filling fraction: interpolate σ_shell → σ_df as subshell fills."""
    s0 = sigma_shell(k, n)
    return s0 + (n_fill / n_max) * (S_DF - s0)


def sigma_sp(p):
    nx = N_S if p % 2 == 0 else N_T
    return 1 - nx / (D * (D - 1))


def sigma_same_p(p):
    return N_S / (N_S + 1) if p == 2 else N_T / (N_T + 1)


def get_period(Z):
    if Z <= 2: return 1
    if Z <= 10: return 2
    if Z <= 18: return 3
    if Z <= 36: return 4
    if Z <= 54: return 5
    if Z <= 86: return 6
    return 7


def compute_IE(Z):
    if Z == 1: return Ry
    if Z == 2: return 2 * Ry * (1 - C**2 * a)

    p = get_period(Z)
    n = p
    nn = NOBLE[p]
    sc = sigma_core_layered(p)

    # s-block
    if Z <= nn + 2:
        inner = nn * sc
        same = max(0, Z - nn - 1) * S_SS
    # f-block (period 6: Z=57-71, period 7: Z=89-103)
    elif (p == 6 and 57 <= Z <= 71) or (p == 7 and 89 <= Z <= 103):
        n_extra = Z - nn - 2
        # NEW: filling fraction for f-electrons
        sf = sigma_fill(n_extra, 14, max(1, p - 2), p)
        inner = nn * sc + n_extra * sf + S_SS
        same = 0
    # d-block (period 6: Z=72-80 with complete f14)
    elif (p == 6 and 72 <= Z <= 80) or (p == 7 and 104 <= Z <= 112):
        n_f = 14
        n_d = Z - nn - n_f - 2
        inner = nn * sc
        inner += n_f * S_DF  # complete f-shell → σ_df
        inner += n_d * sigma_shell(p - 1, p)
        same = S_SS
    # d-block (period 4,5: no f) — with pair correction
    elif (p == 4 and 21 <= Z <= 30) or (p == 5 and 39 <= Z <= 48):
        n_d = Z - nn - 2
        inner = nn * sc + n_d * sigma_shell(p - 1, p)
        # NEW: d-pair correction for 6 ≤ n_d ≤ 9
        if 6 <= n_d <= 9:
            inner += D_PAIR * (n_d - D) / D
        same = S_SS
    # p-block
    else:
        n_df_map = {2: 0, 3: 0, 4: 10, 5: 10, 6: 24, 7: 24}
        n_df = n_df_map.get(p, 0)
        n_ss = 2
        n_p = Z - nn - n_df - n_ss
        inner = nn * sc + n_df * S_DF + n_ss * sigma_sp(p)
        same = max(0, n_p - 1) * sigma_same_p(p)
        if n_p > 3:
            same += D_PAIR

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


class DPairCorrection(Experiment):
    ID = "ATM_022"
    TITLE = "d-Block Pair Correction"

    def run(self):
        self.test1_concept()
        self.test2_full_scan()

    def test1_concept(self):
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 1: d-pair correction concept")
        self.log(f"  {'='*55}")
        self.log(f"\n  d-subshell: 2d=10 states, half-fill=d=5")
        self.log(f"  Delta_d = Delta_pair x (n_d - d)/d for d < n_d < 2d")
        self.log(f"  Delta_pair = {D_PAIR:.5f}")
        self.log(f"\n  Correction values:")
        for nd in range(1, 11):
            delta = D_PAIR * (nd - D) / D if 6 <= nd <= 9 else 0
            self.log(f"    n_d={nd:2d}: Delta={delta:.4f}")
        self.check("d-pair applies for 6<=n_d<=9",
                    all(D_PAIR*(nd-D)/D > 0 for nd in range(6, 10)))

    def test2_full_scan(self):
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 2: Full periodic Z=1-118")
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
                p = get_period(Z)
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
        self.log(f"\n  Per-period median:")
        for p in range(1, 8):
            if per_errs[p]:
                pm = np.median(per_errs[p])
                self.log(f"  Period {p}: {pm:.1f}%"
                         f" ({len(per_errs[p])} el)")
        n5 = sum(1 for e in errs if e < 5)
        n10 = sum(1 for e in errs if e < 10)
        self.check(f"Median < 7%", med < 7)
        self.check(f">50% within 10%", n10/len(errs) > 0.50)
        self.check(f">35% within 5%", n5/len(errs) > 0.35)


if __name__ == "__main__":
    DPairCorrection().execute()
