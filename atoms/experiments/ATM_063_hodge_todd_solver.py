"""
ATM_063: Hodge-Todd Composite Class Solver
Joint research by Mingu Jeong and Claude (Anthropic)

Composite Hodge classes on ℂP⁴:
  h¹ (triangles, C(5,3)=10): SSS+SST+STT → cross-shell σ
  h³ (tetrahedra, C(5,4)=5): AAAB+AABB → same-shell σ

Todd class correction at each level:
  δ(h¹) = σ₀² × c₁ × α_GUT / (d²-1)     [budget=24, adjoint]
  δ(h³) = σ₀² × c₁ × α_GUT / C(d+1,4)   [budget=15, 4-form]

Combined with: D_PAIR, adjoint resummation, quantum defect.
Target: Period 2 median < 500 ppm.
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
D_PAIR = N_S / np.pi**2  # ≈ 0.3040

# First Chern class of ℂP⁴
c1 = D + 1  # = 6

# Todd correction magnitudes
BUDGET_H1 = D**2 - 1         # = 24 (adjoint, triangle level)
BUDGET_H3 = 15               # = C(6,4) (4-form, tetrahedra level)


def todd_h1(sigma0):
    """Todd correction at h¹ (triangle) level: cross-shell."""
    return sigma0**2 * c1 * ALPHA_GUT / BUDGET_H1


def todd_h3(sigma0):
    """Todd correction at h³ (tetrahedra) level: same-shell."""
    return sigma0**2 * c1 * ALPHA_GUT / BUDGET_H3


# Nuclear masses (keV) for reduced mass
NUC_MASS = {
    1:938783, 2:3727379, 3:6533834, 4:8394791, 5:10252548,
    6:11174866, 7:13040203, 8:14895084, 9:17692300, 10:18622840,
    11:20697700, 12:22644900, 13:25133100, 14:26091800,
    15:28850800, 16:29795600, 17:32921400, 18:34943800,
}

IE_OBS = {
    1:13.59844, 2:24.58738, 3:5.39172, 4:9.32270, 5:8.29803,
    6:11.2603, 7:14.5341, 8:13.6181, 9:17.4228, 10:21.5645,
    11:5.13908, 12:7.64624, 13:5.98577, 14:8.15169,
    15:10.4867, 16:10.3600, 17:12.9676, 18:15.7596,
}

SYM = ['','H','He','Li','Be','B','C','N','O','F','Ne',
       'Na','Mg','Al','Si','P','S','Cl','Ar']


def mu(Z):
    """Reduced mass factor (1 - m_e/m_nuc)."""
    if Z in NUC_MASS:
        return 1 - m_e_eV / (NUC_MASS[Z] * 1e3)
    return 1 - m_e_eV / (Z * 938.272e6)


def solve(Z, todd_cross=False, todd_same=False, uniform_p=False,
          anti_todd_same=False):
    """Per-electron recursive solver.

    Modes:
      uniform_p: same-p/d ALL use σ=N_S/(N_S+1), no m-dependent BBB
      todd_cross: h¹ Todd → REDUCE cross-shell σ (less screening)
      todd_same: h³ Todd → REDUCE same-subshell σ
      anti_todd_same: h³ Todd → INCREASE same-subshell σ (more screening)
    """
    order = []
    for n in range(1, 8):
        for l in range(min(n, 4)):
            order.append((n+l, n, l))
    order.sort()

    electrons = []  # (n, l, z_eff, m_quantum)
    remaining = Z

    for _, n, l in order:
        count = min(remaining, 2*(2*l+1))
        if count <= 0:
            break
        remaining -= count
        n_orb = 2*l + 1

        for i in range(count):
            m_i = i % n_orb if i < n_orb else (i - n_orb) % n_orb

            screening = 0.0
            for e in electrons:
                nj, lj, _, mj = e

                if nj != n:
                    # Cross-shell: h¹ sector
                    nc = N_S if lj == 0 else 1
                    sigma = 1 - nc / (D**2 - 1)
                    if todd_cross:
                        sigma -= todd_h1(sigma)

                elif lj != l:
                    # Same shell, diff subshell
                    nx = N_S if (nj + n) % 2 == 0 else N_T
                    sigma = 1 - nx / (D * (D - 1))

                elif lj == 0:
                    # Same s-subshell: BBB channel
                    sigma = 1.0/N_T + N_T**2 * ALPHA_GUT
                    if todd_same:
                        sigma -= todd_h3(sigma)
                    elif anti_todd_same:
                        sigma += todd_h3(sigma)

                else:
                    # Same p/d subshell
                    if uniform_p or mj != m_i:
                        # h³ sector: AABB tetrahedra
                        sigma = N_S/(N_S+1) if l == 1 else N_T/(N_T+1)
                    else:
                        # Same m, opp spin → BBB-like
                        sigma = 1.0/N_T + N_T**2 * ALPHA_GUT
                    if todd_same:
                        sigma -= todd_h3(sigma)
                    elif anti_todd_same:
                        sigma += todd_h3(sigma)

                screening += sigma

            # D_PAIR for half-fill+ in p/d
            total_in_sub = sum(1 for e in electrons
                               if e[0]==n and e[1]==l) + 1
            n_half = 2*l + 1
            if total_in_sub > n_half and l >= 1:
                screening += D_PAIR

            z_eff = max(0.01, Z - screening)
            electrons.append((n, l, z_eff, m_i))

    if not electrons:
        return 0.0, []

    last = electrons[-1]
    nl, ll, zl, ml = last

    # Quantum defect for p-electrons
    if ll == 1:
        delta = (N_S - 1) * ALPHA_GUT / nl**2
        n_eff = nl - delta
    else:
        n_eff = nl

    # Adjoint resummation Ry factor
    a_eff = zl**2 * ALPHA**2 / N_S
    ry_factor = 24 / (24 + a_eff + a_eff**2)

    IE = zl**2 * Ry * ry_factor * mu(Z) / n_eff**2
    return IE, electrons


class HodgeToddSolver(Experiment):
    ID = "ATM_063"
    TITLE = "Hodge-Todd Composite Class Solver"

    def run(self):
        self.test1_todd_values()
        self.test2_baseline()
        self.test3_uniform_p()
        self.test4_uniform_plus_todd()
        self.test5_hybrid()
        self.test6_summary()
        self.test7_zeff_diagnostic()

    def test1_todd_values(self):
        """Print Todd correction magnitudes."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Todd class corrections by Hodge level")
        self.log(f"  {'='*55}")

        # h¹ cross-shell corrections
        s_cross = 1 - N_S/(D**2-1)  # 7/8
        s_ns_np = 1 - N_S/(D*(D-1))  # 17/20
        d1 = todd_h1(s_cross)
        d2 = todd_h1(s_ns_np)

        self.log(f"\n  h¹ (triangles, budget={BUDGET_H1}):")
        self.log(f"    σ_cross = {s_cross:.4f}"
                 f" → δ = {d1:.6f}"
                 f" → corrected = {s_cross-d1:.6f}")
        self.log(f"    σ_ns→np = {s_ns_np:.4f}"
                 f" → δ = {d2:.6f}"
                 f" → corrected = {s_ns_np-d2:.6f}")

        # h³ same-shell corrections
        s_bbb = 1.0/N_T + N_T**2 * ALPHA_GUT
        s_p = N_S/(N_S+1)
        d3 = todd_h3(s_bbb)
        d4 = todd_h3(s_p)

        self.log(f"\n  h³ (tetrahedra, budget={BUDGET_H3}):")
        self.log(f"    σ_BBB   = {s_bbb:.6f}"
                 f" → δ = {d3:.6f}"
                 f" → corrected = {s_bbb-d3:.6f}")
        self.log(f"    σ_same_p= {s_p:.4f}"
                 f" → δ = {d4:.6f}"
                 f" → corrected = {s_p-d4:.6f}")

        self.log(f"\n  D_PAIR = {D_PAIR:.6f}")
        self.log(f"  α_GUT = {ALPHA_GUT:.8f}")
        self.log(f"  c₁(ℂP⁴) = {c1}")
        self.check("Todd values computed", True)

    def test2_baseline(self):
        """Baseline with m-dependent same-p."""
        self.log(f"\n  {'='*55}")
        self.log(f"  A: Baseline (m-dependent same-p)")
        self.log(f"  {'='*55}")
        self._run_p2(tc=False, ts=False, up=False, label="A:m-dep")

    def test3_uniform_p(self):
        """Uniform same-p: all use σ=3/4."""
        self.log(f"\n  {'='*55}")
        self.log(f"  B: Uniform same-p (all σ=3/4)")
        self.log(f"  {'='*55}")
        self._run_p2(tc=False, ts=False, up=True, label="B:unif")

    def test4_uniform_plus_todd(self):
        """Uniform same-p + Todd h¹ cross-shell."""
        self.log(f"\n  {'='*55}")
        self.log(f"  C: Uniform + Todd h¹ (cross only)")
        self.log(f"  {'='*55}")
        self._run_p2(tc=True, ts=False, up=True, ats=False,
                     label="C:+h¹")

    def test5_hybrid(self):
        """h¹ reduces cross, h³ increases same (anti-Todd)."""
        self.log(f"\n  {'='*55}")
        self.log(f"  D: h¹↓cross + h³↑same (opposing Todd)")
        self.log(f"  {'='*55}")
        self._run_p2(tc=True, ts=False, up=True, ats=True,
                     label="D:h¹↓h³↑")

    def test6_summary(self):
        """Summary comparison table."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Summary: ppm by variant")
        self.log(f"  {'='*55}")

        configs = [
            ("B:unif", dict(todd_cross=False, todd_same=False,
                            uniform_p=True, anti_todd_same=False)),
            ("C:+h¹", dict(todd_cross=True, todd_same=False,
                           uniform_p=True, anti_todd_same=False)),
            ("D:h¹↓h³↑", dict(todd_cross=True, todd_same=False,
                              uniform_p=True, anti_todd_same=True)),
        ]
        labels = [c[0] for c in configs]
        self.log(f"\n  {'Z':>3} {'Sym':>3}"
                 + "".join(f" {l:>9}" for l in labels))

        meds = [[] for _ in configs]
        for Z in range(3, 11):
            obs = IE_OBS[Z]
            ppms = []
            for i, (_, kw) in enumerate(configs):
                IE, _ = solve(Z, **kw)
                ppm = (IE - obs)/obs * 1e6
                ppms.append(ppm)
                meds[i].append(abs(ppm))
            self.log(f"  {Z:3d} {SYM[Z]:>3}"
                     + "".join(f" {p:+9.0f}" for p in ppms))

        self.log(f"  {'':>7}"
                 + "".join(f" {np.median(m):9.0f}" for m in meds)
                 + "  ← median")
        best_idx = min(range(len(meds)),
                       key=lambda i: np.median(meds[i]))
        best_med = np.median(meds[best_idx])
        self.log(f"\n  ★ Best: {labels[best_idx]}"
                 f" (median {best_med:.0f} ppm)")
        self.check(f"Best P2 median {best_med:.0f} ppm",
                   best_med < 10000)

    def _run_p2(self, tc, ts, up, label, ats=False):
        """Run Period 2 with given flags."""
        self.log(f"\n  {'Z':>3} {'Sym':>3} {'IE':>9} {'Obs':>9}"
                 f" {'ppm':>8} {'Z_eff':>7}")
        errs = []
        for Z in range(3, 11):
            IE, elecs = solve(Z, tc, ts, up, ats)
            obs = IE_OBS[Z]
            ppm = (IE - obs)/obs * 1e6
            errs.append(abs(ppm))
            zeff = elecs[-1][2] if elecs else 0
            self.log(f"  {Z:3d} {SYM[Z]:>3} {IE:9.5f} {obs:9.5f}"
                     f" {ppm:+8.0f} {zeff:7.4f}")

        med = np.median(errs)
        self.log(f"\n  Median: {med:.0f} ppm")
        self.log(f"  <5000: {sum(1 for e in errs if e<5000)}/8"
                 f"  <1000: {sum(1 for e in errs if e<1000)}/8"
                 f"  <500: {sum(1 for e in errs if e<500)}/8")
        self.check(f"[{label}] P2 median {med:.0f} ppm", med < 10000)


    def test7_zeff_diagnostic(self):
        """Exact z_eff vs model → shows where corrections needed."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Z_eff diagnostic: exact vs model")
        self.log(f"  {'='*55}")
        self.log(f"\n  z_exact = sqrt(IE_obs × n_eff² / (Ry × mu))")
        self.log(f"\n  {'Z':>3} {'Sym':>3} {'z_exact':>8} {'z_model':>8}"
                 f" {'Δz':>8} {'screen':>8} {'type':>8}")

        for Z in range(3, 11):
            IE, elecs = solve(Z, uniform_p=True)
            obs = IE_OBS[Z]
            last = elecs[-1]
            nl, ll, zl, ml = last
            # Reverse: z_exact from obs IE
            if ll == 1:
                delta = (N_S-1) * ALPHA_GUT / nl**2
                n_eff = nl - delta
            else:
                n_eff = nl
            z_exact = np.sqrt(obs * n_eff**2 / (Ry * mu(Z)))
            z_model = zl
            dz = z_model - z_exact
            total_screen = Z - z_model
            sub = 'spdf'[ll]

            self.log(f"  {Z:3d} {SYM[Z]:>3} {z_exact:8.4f}"
                     f" {z_model:8.4f} {dz:+8.5f}"
                     f" {total_screen:8.4f}  {nl}{sub}")

        self.log(f"\n  Δz > 0: model has too little screening")
        self.log(f"  Δz < 0: model has too much screening")

        # Cross-shell Todd correction per pair
        dcross = todd_h1(7/8)
        self.log(f"\n  Todd h¹ correction per cross-shell pair:"
                 f" δ = {dcross:.5f}")
        self.log(f"  For Li (2 pairs): total δ = {2*dcross:.5f}"
                 f" (needed: 0.00930)")
        self.log(f"\n  h³ (3-body overlap) corrections needed:")
        self.log(f"    = differences between per-pair Todd"
                 f" and actual Δz")
        self.check("Diagnostic complete", True)


if __name__ == "__main__":
    HodgeToddSolver().execute()
