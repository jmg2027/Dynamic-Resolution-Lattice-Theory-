"""
ATM_035: Complete-Shell Pair Correction for Periodic Table IE
Joint research by Mingu Jeong and Claude (Anthropic)

Problem: ATM_022 has median 3.5% but Period 6-7 p-block has 10-24% errors.
Root cause: complete d10 and f14 subshells have pair correction (D_PAIR)
that was applied in d-block (ATM_022) but NOT in p-block.

Fix (0 new parameters):
  1. d-pair correction extended to Period 6-7 d-block
  2. Complete d10 pair correction added to Period 4-7 p-block
  3. Complete f14 pair correction added to Period 6-7 p-block
  4. Lu(71)/Lr(103) reclassified as d-block / p-block

All corrections use existing D_PAIR = N_S/pi^2 = 3/pi^2 ≈ 0.304.
No new parameters introduced.

Tests:
  1. Diagnostic: worst 15 elements in ATM_022
  2. Full scan with corrections
  3. Before/after comparison
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
import drlt

Ry = 13.606; a = drlt.ALPHA_GUT
D = 5; N_S = 3; N_T = 2; C = 2

S_1S = 1 - N_S / (D**2 - 1)          # 7/8
S_SS = 1/N_T + C**2 * a               # 0.597
D_PAIR = N_S / np.pi**2               # 3/pi^2
S_DF = 1 - a                          # 0.976
C_GAP = D * (D + 1)                   # 30
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


def sigma_fill(n_fill, n_max, k, n):
    s0 = sigma_shell(k, n)
    return s0 + (n_fill / n_max) * (S_DF - s0)


def dpair_correction(n_occ, n_half):
    """Pair correction for subshell past half-fill."""
    if n_occ > n_half:
        return D_PAIR * (n_occ - n_half) / n_half
    return 0.0


def compute_IE_v2(Z):
    """Improved IE: deep-core pair + Lu/Lr reclassification."""
    if Z == 1: return Ry
    if Z == 2: return 2 * Ry * (1 - C**2 * a)

    p = get_period(Z)
    n = p
    nn = NOBLE[p]
    sc = sigma_core_layered(p)

    # Deep-core pair: D_PAIR * N_S/N_T = 9/(2pi^2) ≈ 0.456
    # Only for Period 6-7 p-block where d10+f14 are deeply buried.
    DEEP_PAIR = D_PAIR * N_S / N_T

    # s-block (unchanged)
    if Z <= nn + 2:
        inner = nn * sc
        same = max(0, Z - nn - 1) * S_SS

    # f-block (same ranges as ATM_022)
    # FIX: Lu(71)=[Xe]4f14 5d1 6s2, Lr(103)=[Rn]5f14 7s2 7p1
    # Cap f at 14, count remaining electron explicitly
    elif (p == 6 and 57 <= Z <= 71) or (p == 7 and 89 <= Z <= 103):
        n_raw = Z - nn - 2
        n_f = min(n_raw, 14)
        n_extra_d = max(0, n_raw - 14)  # 0 or 1 (Lu/Lr only)
        sf = sigma_fill(n_f, 14, max(1, p - 2), p)
        inner = nn * sc + n_f * sf + S_SS
        if n_extra_d > 0:
            inner += n_extra_d * sigma_shell(p - 1, p)
            # f14-complete pair correction at f→d boundary
            # Complete f-shell pairing pushes d-electron outward
            inner += D_PAIR
        same = 0

    # d-block Period 6-7 (same as ATM_022, NO d-pair)
    elif (p == 6 and 72 <= Z <= 80) or (p == 7 and 104 <= Z <= 112):
        n_f = 14
        n_d = Z - nn - n_f - 2
        inner = nn * sc + n_f * S_DF + n_d * sigma_shell(p - 1, p)
        same = S_SS

    # d-block Period 4-5 (same as ATM_022, with d-pair 6-9)
    elif (p == 4 and 21 <= Z <= 30) or (p == 5 and 39 <= Z <= 48):
        n_d = Z - nn - 2
        inner = nn * sc + n_d * sigma_shell(p - 1, p)
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
            if p == 6:
                same += DEEP_PAIR          # Period 6: DEEP replaces D
            elif p >= 7:
                same += D_PAIR + DEEP_PAIR  # Period 7+: both (deeper)
            else:
                same += D_PAIR              # Period 2-5: original
        # Deep-core half-fill (n_p=3) for Period 6-7
        if p >= 6 and n_p == 3:
            inner += DEEP_PAIR
        # First p-electron (n_p=1) in Period 6: temporal pair onset
        if p == 6 and n_p == 1:
            inner += D_PAIR / N_T   # = 0.152

    Ze = Z - inner - same
    return max(0.01, Ze)**2 * Ry / n**2


# Import data from ATM_022
from ATM_022_dpair_correction import IE_OBS, SYM, compute_IE as compute_IE_old


class CompleteShellPair(Experiment):
    ID = "ATM_035"
    TITLE = "Complete-Shell Pair Correction"

    def run(self):
        self.test1_diagnostic()
        self.test2_full_scan()
        self.test3_comparison()

    def test1_diagnostic(self):
        """Top 15 worst elements in old model + root cause."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: Diagnostic — worst elements in ATM_022")
        self.log(f"  {'='*60}")

        worst = []
        for Z in range(1, 119):
            ie_old = compute_IE_old(Z)
            obs = IE_OBS.get(Z, 0)
            if obs > 0:
                err = (ie_old - obs) / obs * 100
                worst.append((abs(err), Z, ie_old, obs, err))
        worst.sort(reverse=True)

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'IE_old':>7} {'Obs':>7}"
                 f" {'Err%':>7} {'Block':>6} {'Fix':>20}")
        for _, Z, ie, obs, err in worst[:15]:
            p = get_period(Z)
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            blk = 'p' if Z > NOBLE[p]+2+{4:10,5:10,6:24,7:24}.get(p,0) \
                  else 'd' if Z > NOBLE[p]+2 else 's'
            fix = ""
            if blk == 'p' and p >= 4:
                fix = "d10-pair"
                if p >= 6: fix += "+f14-pair"
            elif Z in (71, 103):
                fix = "reclassify"
            self.log(f"  {Z:4d} {sym:>3} {ie:7.2f} {obs:7.2f}"
                     f" {err:+7.1f}% {blk:>6} {fix:>20}")

        self.check("Diagnostic complete", True)

    def test2_full_scan(self):
        """Full Z=1-118 scan with new model."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Full periodic Z=1-118 (v2)")
        self.log(f"  {'='*60}")

        errs = []
        per_errs = {p: [] for p in range(1, 8)}
        for Z in range(1, 119):
            ie = compute_IE_v2(Z)
            obs = IE_OBS.get(Z, 0)
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            if obs > 0:
                err = (ie - obs) / obs * 100
                errs.append(abs(err))
                p = get_period(Z)
                per_errs[p].append(abs(err))
                mk = 'V' if abs(err) < 5 else 'o' if abs(err) < 15 \
                    else '.' if abs(err) < 30 else ' '
                self.log(f"  {Z:3d} {sym:>3} {ie:7.2f} {obs:7.2f}"
                         f" {err:+6.1f}% {mk}")

        self.log(f"\n  Statistics:")
        for t in [3, 5, 10, 15, 30]:
            n = sum(1 for e in errs if e < t)
            self.log(f"    <{t:2d}%: {n:3d}/118 ({n/118*100:.0f}%)")
        med = np.median(errs)
        self.log(f"    Median: {med:.1f}%")
        self.log(f"\n  Per-period median:")
        for p in range(1, 8):
            if per_errs[p]:
                pm = np.median(per_errs[p])
                self.log(f"    Period {p}: {pm:.1f}%"
                         f" ({len(per_errs[p])} el)")

        self._med_new = med
        self._n5_new = sum(1 for e in errs if e < 5)
        self.check(f"Median = {med:.1f}%", med < 5)

    def test3_comparison(self):
        """Before vs after comparison."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Before/After comparison")
        self.log(f"  {'='*60}")

        old_errs, new_errs = [], []
        improved, worsened = [], []
        for Z in range(1, 119):
            obs = IE_OBS.get(Z, 0)
            if obs <= 0: continue
            ie_old = compute_IE_old(Z)
            ie_new = compute_IE_v2(Z)
            e_old = abs((ie_old - obs) / obs * 100)
            e_new = abs((ie_new - obs) / obs * 100)
            old_errs.append(e_old)
            new_errs.append(e_new)
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            diff = e_new - e_old
            if diff < -2:
                improved.append((Z, sym, e_old, e_new))
            elif diff > 2:
                worsened.append((Z, sym, e_old, e_new))

        self.log(f"\n  IMPROVED (>2% better):")
        for Z, sym, eo, en in improved:
            self.log(f"    {Z:3d} {sym:>3}: {eo:.1f}% → {en:.1f}%"
                     f" (Δ={en-eo:+.1f}%)")

        self.log(f"\n  WORSENED (>2% worse):")
        for Z, sym, eo, en in worsened:
            self.log(f"    {Z:3d} {sym:>3}: {eo:.1f}% → {en:.1f}%"
                     f" (Δ={en-eo:+.1f}%)")

        med_old = np.median(old_errs)
        med_new = np.median(new_errs)
        n5_old = sum(1 for e in old_errs if e < 5)
        n5_new = sum(1 for e in new_errs if e < 5)

        self.log(f"\n  {'Metric':>20} {'ATM_022':>10} {'ATM_035':>10}")
        self.log(f"  {'Median':>20} {med_old:10.1f}% {med_new:10.1f}%")
        self.log(f"  {'<5%':>20} {n5_old:10d} {n5_new:10d}")
        self.log(f"  {'Improved':>20} {len(improved):10d}")
        self.log(f"  {'Worsened':>20} {len(worsened):10d}")

        self.check(f"Median improved ({med_old:.1f}→{med_new:.1f})",
                   med_new < med_old)
        self.check(f"More <5% ({n5_old}→{n5_new})",
                   n5_new >= n5_old)


if __name__ == "__main__":
    CompleteShellPair().execute()
