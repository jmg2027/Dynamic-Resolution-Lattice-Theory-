"""
EXP_077: Period 2 Screening Analysis — Required σ from IE
Joint research by Mingu Jeong and Claude (Anthropic)

Approach: work BACKWARDS from observed IE to find required Z_eff,
then decompose into inner/same-shell screening to find DRLT formula.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
import drlt

Ry = 13.606
a = drlt.ALPHA_GUT; ae = drlt.ALPHA_EM
D = 5; N_S = 3; N_T = 2
sigma_78 = 1 - N_S/(D**2-1)  # 7/8

IE_OBS = {1:13.598, 2:24.587, 3:5.392, 4:9.323, 5:8.298,
          6:11.260, 7:14.534, 8:13.618, 9:17.423, 10:21.565}
SYMS = ['','H','He','Li','Be','B','C','N','O','F','Ne']

# Electron structure: (n_shell, n_inner, n_same_shell)
STRUCT = {
    3: (2, 2, 0),   # Li: 1s² | 2s¹
    4: (2, 2, 1),   # Be: 1s² | 2s²
    5: (2, 4, 0),   # B:  1s²2s² | 2p¹
    6: (2, 4, 1),   # C:  1s²2s² | 2p²
    7: (2, 4, 2),   # N:  1s²2s² | 2p³
    8: (2, 4, 3),   # O:  1s²2s² | 2p⁴
    9: (2, 4, 4),   # F:  1s²2s² | 2p⁵
    10:(2, 4, 5),   # Ne: 1s²2s² | 2p⁶
}


class ScreeningAnalysis(Experiment):
    ID = "077"
    TITLE = "Period 2 Screening Analysis"

    def run(self):
        self.test1_required_zeff()
        self.test2_decompose_screening()
        self.test3_candidate_formulas()

    def test1_required_zeff(self):
        self.log(f"\n  {'═'*50}")
        self.log(f"  Test 1: Required Z_eff from Observed IE")
        self.log(f"  {'═'*50}\n")

        for Z in range(3, 11):
            n, n_in, n_same = STRUCT[Z]
            IE = IE_OBS[Z]
            Z_eff = n * np.sqrt(IE / Ry)
            screen = Z - Z_eff
            n_total = n_in + n_same
            per = screen / n_total if n_total > 0 else 0
            self.log(f"  Z={Z} {SYMS[Z]:>3}: Z_eff={Z_eff:.3f},"
                     f" screen={screen:.3f}, per_e={per:.4f}")

        self.check("Z_eff analysis complete", True)

    def test2_decompose_screening(self):
        self.log(f"\n  {'═'*50}")
        self.log(f"  Test 2: Inner vs Same-Shell Decomposition")
        self.log(f"  {'═'*50}")

        # Li → σ_inner (1s screening of 2s)
        Z_eff_Li = 2 * np.sqrt(IE_OBS[3] / Ry)
        sigma_1s = (3 - Z_eff_Li) / 2
        self.log(f"\n  Li: σ_1s = {sigma_1s:.4f} (DRLT 7/8={sigma_78:.4f})")

        # B → σ_2s→2p (assuming 1s screens with 7/8)
        Z_eff_B = 2 * np.sqrt(IE_OBS[5] / Ry)
        sigma_2s = (5 - Z_eff_B - 2*sigma_78) / 2
        self.log(f"  B: σ_2s→2p = {sigma_2s:.4f}")

        # Be → σ_same_2s
        Z_eff_Be = 2 * np.sqrt(IE_OBS[4] / Ry)
        sigma_same_s = 4 - Z_eff_Be - 2*sigma_78
        self.log(f"  Be: σ_same_2s = {sigma_same_s:.4f}")

        # p-shell same-screening
        self.log(f"\n  p-shell σ_same:")
        for Z in range(6, 11):
            n, n_in, n_same = STRUCT[Z]
            Z_eff = 2 * np.sqrt(IE_OBS[Z] / Ry)
            inner = 2*sigma_78 + 2*sigma_2s
            same = (Z - Z_eff - inner) / n_same if n_same > 0 else 0
            self.log(f"    Z={Z} ({SYMS[Z]}): σ_p={same:.4f}")

        self.check("Decomposition complete", True)

    def test3_candidate_formulas(self):
        self.log(f"\n  {'═'*50}")
        self.log(f"  Test 3: Candidate IE Formulas")
        self.log(f"  {'═'*50}")

        # Get calibrated values from test2
        Z_eff_Li = 2*np.sqrt(IE_OBS[3]/Ry)
        Z_eff_B = 2*np.sqrt(IE_OBS[5]/Ry)
        sigma_2s_p = (5-Z_eff_B-2*sigma_78)/2

        # Formula A: current (σ_inner=7/8, σ_same=0.549)
        def ie_A(Z):
            n,ni,ns = STRUCT[Z]
            Ze = Z - ni*sigma_78 - ns*(1/N_T+N_T*a)
            return max(0.1,Ze)**2 * Ry/n**2

        # Formula B: all σ=7/8
        def ie_B(Z):
            n,ni,ns = STRUCT[Z]
            Ze = Z - (ni+ns)*sigma_78
            return max(0.1,Ze)**2 * Ry/n**2

        # Formula C: calibrated (σ_1s=7/8, σ_2s from B)
        def ie_C(Z):
            n,ni,ns = STRUCT[Z]
            n1s = min(ni,2); n2s = ni-n1s
            inner = n1s*sigma_78 + n2s*sigma_2s_p
            same = ns*(1/N_T+N_T*a)
            Ze = Z - inner - same
            return max(0.1,Ze)**2 * Ry/n**2

        self.log(f"\n  Z Sym  IE_obs   A(σ=0.55)  B(σ=7/8)  C(calib)")
        for Z in range(3, 11):
            ie = IE_OBS[Z]
            A=ie_A(Z); B=ie_B(Z); C=ie_C(Z)
            eA=(A-ie)/ie*100; eB=(B-ie)/ie*100; eC=(C-ie)/ie*100
            self.log(f"  {Z:2d} {SYMS[Z]:>3} {ie:6.3f}  "
                     f"{A:6.2f}({eA:+5.1f}%)  "
                     f"{B:6.2f}({eB:+5.1f}%)  "
                     f"{C:6.2f}({eC:+5.1f}%)")

        self.check("Formula comparison done", True)


if __name__ == "__main__":
    ScreeningAnalysis().execute()
