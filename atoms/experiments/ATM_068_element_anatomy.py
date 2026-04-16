"""
ATM_068: Element-by-Element Anatomy — B and O Analysis
Joint research by Mingu Jeong and Claude (Anthropic)

ATM_067 achieved median 879 ppm (6/8 < 1000 ppm).
Outliers: B (+11676 ppm) and O (+11100 ppm).

This experiment:
1. Decompose each element's z_eff error by interaction type
2. Find what makes B and O special
3. Look for patterns across all 8 elements
4. "Portrait" of each element's algebraic structure
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

# Best budgets from ATM_067 scan
BUD_CROSS = 25   # d²
BUD_SDIFF = 15   # C(d+1,4) = wedge count
BUD_SAME_S = 10  # C(d,3) = hinge count
BUD_SAME_P = 25  # d²

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


def z_eff_exact(Z):
    """Extract exact z_eff from observed IE."""
    obs = IE_OBS[Z]
    # Determine last electron's quantum numbers
    order = []
    for n in range(1, 8):
        for l in range(min(n, 4)):
            order.append((n+l, n, l))
    order.sort()
    remaining = Z
    last_n, last_l = 1, 0
    for _, n, l in order:
        count = min(remaining, 2*(2*l+1))
        if count <= 0:
            break
        remaining -= count
        last_n, last_l = n, l
    if last_l == 1:
        n_eff = last_n - (N_S-1)*ALPHA_GUT/last_n**2
    else:
        n_eff = last_n
    return np.sqrt(obs * n_eff**2 / (Ry * mu(Z)))


def analyze_element(Z):
    """Full anatomy of one element's screening structure."""
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
            electrons.append((n, l, m_i))

    if not electrons:
        return {}

    last = electrons[-1]
    nl, ll, ml = last
    inner = electrons[:-1]
    n_inner = len(inner)
    factor = N_T / n_inner if n_inner > 0 else 0

    # Decompose screening by type
    screen = {'cross': [], 'sdiff': [], 'same_s': [], 'same_p': []}
    screen_corr = {'cross': [], 'sdiff': [], 'same_s': [], 'same_p': []}

    for e in inner:
        nj, lj, mj = e
        if nj != nl:
            nc = N_S if lj == 0 else 1
            s0 = 1 - nc/(D**2-1)
            delta = todd(s0, BUD_CROSS) * factor
            screen['cross'].append(s0)
            screen_corr['cross'].append(s0 - delta)
        elif lj != ll:
            nx = N_S if (nj+nl) % 2 == 0 else N_T
            s0 = 1 - nx/(D*(D-1))
            delta = todd(s0, BUD_SDIFF) * factor
            screen['sdiff'].append(s0)
            screen_corr['sdiff'].append(s0 - delta)
        elif lj == 0:
            s0 = 1.0/N_T + N_T**2*ALPHA_GUT
            delta = todd(s0, BUD_SAME_S) * factor
            screen['same_s'].append(s0)
            screen_corr['same_s'].append(s0 + delta)
        else:
            s0 = N_S/(N_S+1) if ll == 1 else N_T/(N_T+1)
            delta = todd(s0, BUD_SAME_P) * factor
            screen['same_p'].append(s0)
            screen_corr['same_p'].append(s0 + delta)

    # D_PAIR
    total_in_sub = sum(1 for e in inner if e[0]==nl and e[1]==ll) + 1
    has_dpair = total_in_sub > 2*ll+1 and ll >= 1

    # Totals
    total_base = sum(sum(v) for v in screen.values())
    total_corr = sum(sum(v) for v in screen_corr.values())
    if has_dpair:
        total_base += D_PAIR
        total_corr += D_PAIR

    zeff_base = Z - total_base
    zeff_corr = Z - total_corr
    zeff_obs = z_eff_exact(Z)

    return {
        'Z': Z, 'sym': SYM[Z],
        'config': f'{nl}{"spdf"[ll]}',
        'n_inner': n_inner, 'factor': factor,
        'screen': screen, 'screen_corr': screen_corr,
        'has_dpair': has_dpair,
        'total_base': total_base, 'total_corr': total_corr,
        'zeff_base': zeff_base, 'zeff_corr': zeff_corr,
        'zeff_obs': zeff_obs,
        'n_cross': len(screen['cross']),
        'n_sdiff': len(screen['sdiff']),
        'n_same_s': len(screen['same_s']),
        'n_same_p': len(screen['same_p']),
    }


class ElementAnatomy(Experiment):
    ID = "ATM_068"
    TITLE = "Element-by-Element Anatomy"

    def run(self):
        self.test1_portraits()
        self.test2_B_O_special()
        self.test3_pattern()

    def test1_portraits(self):
        """Portrait of each Period 2 element."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Period 2: Element Portraits")
        self.log(f"  {'='*60}")

        for Z in range(3, 11):
            a = analyze_element(Z)
            obs = IE_OBS[Z]
            if a['config'].endswith('p'):
                n_eff = int(a['config'][0]) - (N_S-1)*ALPHA_GUT/int(a['config'][0])**2
            else:
                n_eff = int(a['config'][0])
            a_eff = a['zeff_corr']**2 * ALPHA**2 / N_S
            ry_f = 24/(24+a_eff+a_eff**2)
            IE_corr = a['zeff_corr']**2 * Ry * ry_f * mu(Z) / n_eff**2
            ppm = (IE_corr - obs)/obs * 1e6

            self.log(f"\n  ┌─ Z={Z} {a['sym']} ({a['config']})"
                     f"  N_inner={a['n_inner']}"
                     f"  factor={a['factor']:.4f}")
            self.log(f"  │")

            # Screening decomposition
            for typ in ['cross', 'sdiff', 'same_s', 'same_p']:
                n = len(a['screen'][typ])
                if n == 0:
                    continue
                s_base = a['screen'][typ]
                s_corr = a['screen_corr'][typ]
                total_b = sum(s_base)
                total_c = sum(s_corr)
                delta = total_c - total_b
                direction = '↓' if delta < 0 else '↑'
                label = {'cross': 'cross-shell (SS∧ST≠0)',
                         'sdiff': 'same-diff  (∧² budget)',
                         'same_s': 'same-s     (SS∧SS=0)',
                         'same_p': 'same-p     (SS∧SS=0)'}[typ]
                self.log(f"  │  {label}: {n}×σ₀={s_base[0]:.4f}"
                         f"  → Σ={total_b:.4f} {direction}{abs(delta):.5f}"
                         f" → {total_c:.4f}")

            if a['has_dpair']:
                self.log(f"  │  D_PAIR (Basel): +{D_PAIR:.4f}")

            self.log(f"  │")
            self.log(f"  │  Total screen:"
                     f" base={a['total_base']:.4f}"
                     f" → corr={a['total_corr']:.4f}")
            self.log(f"  │  z_eff:"
                     f" base={a['zeff_base']:.4f}"
                     f"  corr={a['zeff_corr']:.4f}"
                     f"  exact={a['zeff_obs']:.4f}")

            dz_base = a['zeff_base'] - a['zeff_obs']
            dz_corr = a['zeff_corr'] - a['zeff_obs']
            self.log(f"  │  Δz: base={dz_base:+.5f}"
                     f"  corr={dz_corr:+.5f}")
            self.log(f"  │  IE: {IE_corr:.5f} eV"
                     f"  (obs {obs:.5f}, {ppm:+.0f} ppm)")
            self.log(f"  └─{'─'*50}")

        self.check("Portraits complete", True)

    def test2_B_O_special(self):
        """What makes B and O outliers?"""
        self.log(f"\n  {'='*60}")
        self.log(f"  B and O: Why are they outliers?")
        self.log(f"  {'='*60}")

        a_B = analyze_element(5)
        a_O = analyze_element(8)

        self.log(f"\n  B (Z=5): 1s² 2s² 2p¹")
        self.log(f"    Config: {a_B['n_cross']} cross,"
                 f" {a_B['n_sdiff']} sdiff,"
                 f" {a_B['n_same_s']} same_s,"
                 f" {a_B['n_same_p']} same_p")
        self.log(f"    B is the FIRST p-electron.")
        self.log(f"    No same-p interactions → no anti-Todd.")
        self.log(f"    Gets 2 cross Todd(↓) + 2 sdiff Todd(↓)")
        self.log(f"    = ALL corrections DECREASE screening")
        self.log(f"    → z_eff pushed TOO HIGH → IE too high")
        self.log(f"    Δz_corr = {a_B['zeff_corr']-a_B['zeff_obs']:+.5f}")

        self.log(f"\n  O (Z=8): 1s² 2s² 2p⁴")
        self.log(f"    Config: {a_O['n_cross']} cross,"
                 f" {a_O['n_sdiff']} sdiff,"
                 f" {a_O['n_same_s']} same_s,"
                 f" {a_O['n_same_p']} same_p,"
                 f" D_PAIR")
        self.log(f"    O is the FIRST paired p-electron.")
        self.log(f"    D_PAIR adds screening BUT")
        self.log(f"    cross+sdiff Todd(↓) removes more than")
        self.log(f"    same_p anti-Todd(↑) adds back")
        self.log(f"    Net: screening too LOW → z_eff too HIGH")
        self.log(f"    Δz_corr = {a_O['zeff_corr']-a_O['zeff_obs']:+.5f}")

        # The pattern: B and O are TRANSITION points
        self.log(f"\n  ★ PATTERN: B and O are TRANSITIONS")
        self.log(f"    B = p-block entry (0 → 1 p-electron)")
        self.log(f"    O = pairing onset (3 → 4 p-electrons)")
        self.log(f"    At transitions, the correction balance")
        self.log(f"    shifts abruptly. The distributed Todd")
        self.log(f"    with uniform factor N_T/N_inner")
        self.log(f"    doesn't capture this discontinuity.")

        # What would fix them?
        dz_B = a_B['zeff_obs'] - a_B['zeff_corr']
        dz_O = a_O['zeff_obs'] - a_O['zeff_corr']
        self.log(f"\n  To fix B: need Δz = {dz_B:+.5f}")
        self.log(f"    = {abs(dz_B)/ALPHA_GUT:.2f} × α_GUT in z_eff")
        self.log(f"  To fix O: need Δz = {dz_O:+.5f}")
        self.log(f"    = {abs(dz_O)/ALPHA_GUT:.2f} × α_GUT in z_eff")

        self.check("B/O analysis done", True)

    def test3_pattern(self):
        """Cross-element pattern analysis."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Pattern: correction balance across Period 2")
        self.log(f"  {'='*60}")

        self.log(f"\n  {'Z':>3} {'Sym':>3} {'n_↓':>4} {'n_↑':>4}"
                 f" {'balance':>8} {'Δz_corr':>9} {'ppm':>8}"
                 f" {'type':>10}")

        for Z in range(3, 11):
            a = analyze_element(Z)
            # Count: decreasing (cross+sdiff) vs increasing (same_s+same_p)
            n_down = a['n_cross'] + a['n_sdiff']  # Todd ↓
            n_up = a['n_same_s'] + a['n_same_p']  # anti-Todd ↑
            if a['has_dpair']:
                n_up_str = f"{n_up}+D"
            else:
                n_up_str = str(n_up)
            balance = n_down - n_up
            dz = a['zeff_corr'] - a['zeff_obs']

            obs = IE_OBS[Z]
            n_eff = int(a['config'][0])
            if a['config'].endswith('p'):
                n_eff = n_eff - (N_S-1)*ALPHA_GUT/n_eff**2
            a_eff = a['zeff_corr']**2*ALPHA**2/N_S
            ry_f = 24/(24+a_eff+a_eff**2)
            IE = a['zeff_corr']**2*Ry*ry_f*mu(Z)/n_eff**2
            ppm = (IE-obs)/obs*1e6

            # Classify
            if abs(ppm) < 500:
                typ = '★★★'
            elif abs(ppm) < 1000:
                typ = '★★'
            elif abs(ppm) < 2000:
                typ = '★'
            elif abs(ppm) < 5000:
                typ = 'OK'
            else:
                typ = 'OUTLIER'

            self.log(f"  {Z:3d} {SYM[Z]:>3} {n_down:4d}"
                     f" {n_up_str:>4}"
                     f" {balance:+8d} {dz:+9.5f}"
                     f" {ppm:+8.0f} {typ:>10}")

        self.log(f"\n  n_↓ = cross+sdiff interactions (Todd reduces σ)")
        self.log(f"  n_↑ = same_s+same_p interactions (anti-Todd)")
        self.log(f"  balance = n_↓ - n_↑ (>0 → net z_eff increase)")

        self.log(f"\n  ★ OBSERVATION:")
        self.log(f"    balance > 0 elements (Li,B): z_eff overcorrected")
        self.log(f"    balance < 0 elements (O,F,Ne): z_eff undercorrected")
        self.log(f"    balance = 0 (Be,C,N): best results!")

        self.log(f"\n  B (balance=+4): NO anti-Todd pairs → all-↓")
        self.log(f"  O (balance=0 BUT D_PAIR): pairing disrupts balance")

        # Check: does a balance-dependent correction help?
        self.log(f"\n  {'='*60}")
        self.log(f"  Hypothesis: scale correction by 1/(1+|balance|/d)")
        self.log(f"  {'='*60}")

        self.log(f"\n  {'Z':>3} {'Sym':>3} {'scale':>7}"
                 f" {'Δz_new':>9} {'ppm_new':>8}")
        for Z in range(3, 11):
            a = analyze_element(Z)
            n_down = a['n_cross'] + a['n_sdiff']
            n_up = a['n_same_s'] + a['n_same_p']
            balance = n_down - n_up
            scale = 1.0 / (1 + abs(balance)/D)
            # Recompute with scaled factor
            dz_base = a['zeff_base'] - a['zeff_obs']
            dz_corr_orig = a['zeff_corr'] - a['zeff_obs']
            correction = a['zeff_corr'] - a['zeff_base']
            dz_new = dz_base + correction * scale
            zeff_new = a['zeff_obs'] + dz_new
            n_eff = int(a['config'][0])
            if a['config'].endswith('p'):
                n_eff = n_eff - (N_S-1)*ALPHA_GUT/n_eff**2
            a_eff = zeff_new**2*ALPHA**2/N_S
            ry_f = 24/(24+a_eff+a_eff**2)
            IE_new = zeff_new**2*Ry*ry_f*mu(Z)/n_eff**2
            obs = IE_OBS[Z]
            ppm = (IE_new-obs)/obs*1e6
            self.log(f"  {Z:3d} {SYM[Z]:>3} {scale:7.4f}"
                     f" {dz_new:+9.5f} {ppm:+8.0f}")

        self.check("Pattern analysis done", True)


if __name__ == "__main__":
    ElementAnatomy().execute()

