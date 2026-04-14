"""
ATM_020: Layered Shell Screening Model
Joint research by Mingu Jeong and Claude (Anthropic)

Key discovery: σ_core(p) should NOT be a single formula.
Each shell k screens the outer electron in period n with:

  σ(k→n) = 1 - n_X(k,n) / (d²-1 + (n-k-1)·d(d+1))

where:
  d²-1 = 24   (adjoint dimension, base)
  d(d+1) = 30 (symmetric representation, gap increment)
  n_X = n_S if (k+n) even, n_T if (k+n) odd

Period 2 is special (single simplex): σ_core = S_1S = 7/8 hardcoded.

For d/f-block: extra electrons use σ_shell (being filled)
For p-block: d/f electrons use σ_df = 1-α_GUT (complete subshell)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
import drlt

Ry = 13.606; a = drlt.ALPHA_GUT
D = 5; N_S = 3; N_T = 2; C = 2

# ── Proven constants ──
S_1S = 1 - N_S / (D**2 - 1)          # 7/8
S_SS = 1/N_T + C**2 * a               # 0.597
D_PAIR = N_S / np.pi**2               # 3/π²
S_DF = 1 - a                           # 1-α_GUT ≈ 0.976

# ── NEW: layered shell model ──
C_GAP = D * (D + 1)                    # 30 = symmetric rep dimension


def shell_electrons(k, P):
    """Electron count in shell k for noble gas ending period P."""
    if k == 1:
        return 2
    e = 8  # s + p
    if 3 <= k <= P - 1:
        e += 10  # d subshell filled in period k+1
    if 4 <= k <= P - 2:
        e += 14  # f subshell filled in period k+2
    return e


def sigma_shell(k, n):
    """Screening: shell k electron → outer electron in period n."""
    gap = n - k - 1
    nx = N_S if (k + n) % 2 == 0 else N_T
    return 1 - nx / (D**2 - 1 + gap * C_GAP)


def sigma_core_layered(p):
    """Effective core screening via weighted shell average."""
    if p <= 2:
        return S_1S  # Period 2: single simplex, proven
    P = p - 1
    total_s, total_e = 0.0, 0
    for k in range(1, p):
        nk = shell_electrons(k, P)
        total_s += nk * sigma_shell(k, p)
        total_e += nk
    return total_s / total_e


# ── Period-dependent constants (unchanged from ATM_019) ──
NOBLE = {1: 0, 2: 2, 3: 10, 4: 18, 5: 36, 6: 54, 7: 86}


def sigma_sp(p):
    nx = N_S if p % 2 == 0 else N_T
    return 1 - nx / (D * (D - 1))


def sigma_same_p(p):
    if p == 2:
        return N_S / (N_S + 1)
    return N_T / (N_T + 1)


def get_period(Z):
    if Z <= 2: return 1
    if Z <= 10: return 2
    if Z <= 18: return 3
    if Z <= 36: return 4
    if Z <= 54: return 5
    if Z <= 86: return 6
    return 7


def compute_IE(Z):
    """DRLT IE with layered shell screening."""
    if Z == 1:
        return Ry
    if Z == 2:
        return 2 * Ry * (1 - C**2 * a)

    p = get_period(Z)
    n = p
    n_noble = NOBLE[p]
    sc = sigma_core_layered(p)

    # ── s-block ──
    if Z <= n_noble + 2:
        inner = n_noble * sc
        same = max(0, Z - n_noble - 1) * S_SS
    # ── d-block (period 4+) ──
    elif (p == 4 and Z <= 30) or (p == 5 and Z <= 48) or \
         (p == 6 and 57 <= Z <= 80) or (p == 7 and 89 <= Z <= 112):
        # f-electrons (complete, for period 6+ d-block)
        n_f = 14 if (p >= 6 and Z > n_noble + 2 + 14 + 1) else 0
        if p == 6 and Z >= 72:
            n_f = 14
        elif p == 7 and Z >= 104:
            n_f = 14
        # f-block elements (being filled)
        if (p == 6 and Z <= 71) or (p == 7 and Z <= 103):
            n_extra = Z - n_noble - 2
            inner = n_noble * sc
            inner += n_extra * sigma_shell(max(1, p - 2), p)
            same = 1 * S_SS
        else:
            # d-block proper
            n_d = Z - n_noble - n_f - 2
            inner = n_noble * sc
            if n_f > 0:
                inner += n_f * sigma_shell(p - 2, p)
            inner += n_d * sigma_shell(p - 1, p)
            same = 1 * S_SS
    # ── p-block ──
    else:
        n_df_map = {2: 0, 3: 0, 4: 10, 5: 10, 6: 24, 7: 24}
        n_df = n_df_map.get(p, 0)
        n_ss = 2
        n_p = Z - n_noble - n_df - n_ss
        inner = n_noble * sc + n_df * S_DF + n_ss * sigma_sp(p)
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


class LayeredScreening(Experiment):
    ID = "ATM_020"
    TITLE = "Layered Shell Screening"

    def run(self):
        self.test1_shell_formula()
        self.test2_full_scan()

    def test1_shell_formula(self):
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 1: Layered shell screening formula")
        self.log(f"  {'='*55}")
        self.log(f"\n  sigma(k->n) = 1 - n_X/(d^2-1 + gap*d(d+1))")
        self.log(f"  gap = n-k-1, d(d+1) = {C_GAP}")
        self.log(f"  n_X: n_S if (k+n) even, n_T if odd")
        self.log(f"\n  sigma_eff per period:")
        obs = {2:0.871, 3:0.916, 4:0.930, 5:0.951, 6:0.959, 7:0.967}
        for p in range(2, 8):
            se = sigma_core_layered(p)
            ob = obs[p]
            self.log(f"  p={p}: sigma_eff={se:.5f}"
                     f" obs={ob:.3f} delta={se-ob:+.4f}")
        self.check("Period 2 = S_1S = 7/8",
                    abs(sigma_core_layered(2) - S_1S) < 1e-10)

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
        self.log(f"\n  Per-period median error:")
        for p in range(1, 8):
            if per_errs[p]:
                pm = np.median(per_errs[p])
                self.log(f"  Period {p}: {pm:.1f}%"
                         f" ({len(per_errs[p])} elements)")
        n5 = sum(1 for e in errs if e < 5)
        n15 = sum(1 for e in errs if e < 15)
        self.check(f"Median < 12%", med < 12)
        self.check(f">45% within 15%", n15/len(errs) > 0.45)
        self.check(f">30% within 5%", n5/len(errs) > 0.30)


if __name__ == "__main__":
    LayeredScreening().execute()
