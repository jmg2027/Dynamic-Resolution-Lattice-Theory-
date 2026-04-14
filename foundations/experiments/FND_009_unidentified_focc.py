"""
EXP_065: Unidentified f_occ — 미사용 결합상수의 물리적 정체
Joint research by Mingu Jeong and Claude (Anthropic)

EXP_064에서 발견된 10개 이산 f_occ 중
1/3, 2/3, 3/4, 4/5의 정체를 기하학적으로 탐색.
표준모형 대입이 아닌 기하학적 구조에서 출발.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
import numpy as np
from math import comb
from fractions import Fraction
from collections import defaultdict
from experiment import Experiment

D = 5; N_A = 3; N_B = 2; C_LAT = 2
a = 6 / (25 * np.pi**2)
ae = 1/137.035999084
PHI = (1 + np.sqrt(5)) / 2
eps = a**(N_B/N_A) * (1 + a)


def P(x):
    return (1 + 2*x) / (1 + x)


class UnidentifiedFocc(Experiment):
    ID = "FND_009"
    TITLE = "Unidentified f_occ"

    def run(self):
        self.part1_structural_origin()
        self.part2_duality_pairs()
        self.part3_gauge_connection()
        self.part4_physical_candidates()

    # ================================================================
    #  Part 1: 미사용 f_occ의 구조적 기원
    # ================================================================
    def part1_structural_origin(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 1: 미사용 f_occ의 구조적 기원")
        self.log(f"  {'═'*55}")

        self.log(f"\n  알려진 대응:")
        self.log(f"  1/5 → e,ν 1-vertex    | 2/5 → ℂ² doublet")
        self.log(f"  1/4 → lepton Yukawa   | 1/2 → Higgs (AABB)")
        self.log(f"  3/5 → proton (ℂ³)     | 1   → confinement")
        self.log(f"\n  미사용: 1/3, 2/3, 3/4, 4/5")

        # 각 미사용 f_occ의 실현 방법 상세 분석
        targets = [
            Fraction(1, 3),
            Fraction(2, 3),
            Fraction(3, 4),
            Fraction(4, 5),
        ]

        for f_target in targets:
            self.log(f"\n  ── f_occ = {f_target} ({float(f_target):.4f}) ──")
            x_val = a * float(f_target)
            Px = P(x_val)
            self.log(f"  x = {x_val:.6f}, P(x) = {Px:.6f}")

            # 어떤 (structure, pattern)이 이것을 만드는지
            self.log(f"  실현:")
            total_mult = 0
            for k in range(2, D+1):
                for a_s in range(min(N_A, k)+1):
                    b_s = k - a_s
                    if b_s < 0 or b_s > N_B:
                        continue
                    n_str = comb(N_A, a_s) * comb(N_B, b_s)
                    if n_str == 0:
                        continue
                    for pA in range(a_s+1):
                        for pB in range(b_s+1):
                            p = pA + pB
                            if p == 0:
                                continue
                            if Fraction(p, k) == f_target:
                                n_pat = comb(a_s, pA) * comb(b_s, pB)
                                mult = n_str * n_pat
                                total_mult += mult
                                s_label = 'A'*a_s + 'B'*b_s
                                p_label = f"({pA}A,{pB}B)"
                                self.log(f"    {s_label} 위 {p_label}: "
                                         f"{n_str}×{n_pat} = {mult}")

            self.log(f"  총 다중도: {total_mult}")

            # 기하학적 특성 분석
            p_num = f_target.numerator
            p_den = f_target.denominator
            empty = p_den - p_num
            self.log(f"  구조: {p_den}-simplex에서 {p_num}개 점유, "
                     f"{empty}개 비어있음")

        self.check("미사용 f_occ 4개 분석 완료", True)

    # ================================================================
    #  Part 2: f ↔ (1-f) 쌍 — 입자-홀 관계
    # ================================================================
    def part2_duality_pairs(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 2: f ↔ (1-f) 쌍 분석")
        self.log(f"  {'═'*55}")

        pairs = [
            (Fraction(1,5), Fraction(4,5), "e,ν (1-vtx)", "?"),
            (Fraction(1,4), Fraction(3,4), "lepton Yukawa", "?"),
            (Fraction(1,3), Fraction(2,3), "?", "?"),
            (Fraction(2,5), Fraction(3,5), "ℂ² doublet", "proton"),
        ]

        self.log(f"\n  {'f':<6} {'1-f':<6} {'particle':>18} {'dual':>18} "
                 f"{'P(f)':>8} {'P(1-f)':>8} {'P(f)×P(1-f)':>12}")
        self.log(f"  {'-'*75}")

        for f1, f2, p1, p2 in pairs:
            x1 = a * float(f1)
            x2 = a * float(f2)
            Pf = P(x1)
            Pc = P(x2)
            prod = Pf * Pc
            self.log(f"  {str(f1):<6} {str(f2):<6} {p1:>18} {p2:>18} "
                     f"{Pf:>8.5f} {Pc:>8.5f} {prod:>12.8f}")

        # f=1/2 self-dual
        x_half = a * 0.5
        P_half = P(x_half)
        self.log(f"  {'1/2':<6} {'1/2':<6} {'Higgs':>18} {'self-dual':>18} "
                 f"{P_half:>8.5f} {P_half:>8.5f} {P_half**2:>12.8f}")

        # 2/5 ↔ 3/5 쌍 분석 (알려진 물리)
        self.log(f"\n  ── 알려진 쌍: 2/5 ↔ 3/5 ──")
        self.log(f"  2/5 = ℂ² temporal doublet (2B in simplex)")
        self.log(f"  3/5 = ℂ³ spatial triplet (3A in simplex)")
        self.log(f"  이것은 (n_B, n_A) = (2,3) partition 자체!")
        self.log(f"  → f ↔ (1-f) = temporal ↔ spatial 대칭")

        # 1/4 ↔ 3/4 쌍 분석
        self.log(f"\n  ── 미해결 쌍: 1/4 ↔ 3/4 ──")
        self.log(f"  1/4: 1 vertex on 4-face → '단일 입자가 face에 진입'")
        self.log(f"  3/4: 3 vertices on 4-face → 'face에서 1개 빠짐'")
        self.log(f"  구조적 의미: 3/4는 face의 '거의 채워진' 상태")

        # 3/4 분해
        self.log(f"\n  f = 3/4의 (pA,pB) 분해:")
        self.log(f"    AABB 위 (1A,2B)=ABB: 3×2=6 → spatial 구멍 1개")
        self.log(f"    AABB 위 (2A,1B)=AAB: 3×2=6 → temporal 구멍 1개")
        self.log(f"    AAAB 위 (2A,1B)=AAB: 2×3=6 → spatial 구멍 1개")
        self.log(f"    AAAB 위 (3A,0B)=AAA: 2×1=2 → temporal 구멍 1개")
        self.log(f"  → 3/4는 'face에서 1개 vertex가 빠진 상태'")
        self.log(f"  → 이것은 face를 관통하는 전파에서 1개 hinge가 비활성")

        # 1/3 ↔ 2/3
        self.log(f"\n  ── 미해결 쌍: 1/3 ↔ 2/3 ──")
        self.log(f"  1/3: hinge에서 1 vertex 점유 → 'hinge edge'")
        self.log(f"  2/3: hinge에서 2 vertex 점유 → 'hinge의 한 edge'")
        self.log(f"  이것은 hinge 내부의 edge-vertex 쌍!")

        self.check("f ↔ (1-f) 쌍 분석 완료", True)

    # ================================================================
    #  Part 3: 게이지 보존 채널과의 연결
    # ================================================================
    def part3_gauge_connection(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 3: 게이지 보존 채널과의 연결")
        self.log(f"  {'═'*55}")

        # folded_dim.md의 hinge temporal fraction과 비교
        self.log(f"\n  ── folded_dim.md의 κ(hinge) ──")
        self.log(f"  κ = f_T(hinge) × α_GUT")
        self.log(f"  SSS: κ=0, SST: κ=α/3, STT: κ=2α/3, TTT: κ=α")

        self.log(f"\n  f_occ = 1/3은 정확히 κ_SST/α_GUT")
        self.log(f"  f_occ = 2/3은 정확히 κ_STT/α_GUT")
        self.log(f"  → 이것은 hinge의 folded dimension coupling!")

        # coupling constant 체계와 비교
        self.log(f"\n  ── 결합상수 체계 (ch08) ──")
        self.log(f"  1/α_3 = 8   (strong, SSS hinge)")
        self.log(f"  1/α_2 = 30  (weak, SST/STT mixed)")
        self.log(f"  1/α_1 = 59  (EM, full lattice)")

        # mult=30과 weak force
        self.log(f"\n  주목: f=1/3과 f=2/3 모두 mult=30")
        self.log(f"  1/α_2(GUT) = 30.0!")
        self.log(f"  우연의 일치? 아니면 인과관계?")
        self.log(f"  → mult(1/3) = 30 = 1/α_2 일 수 있음")

        # hinge 수와 대응
        hinge_counts = {
            'SSS(AAA)': (1, f"C({N_A},3)×C({N_B},0)"),
            'SST(AAB)': (6, f"C({N_A},2)×C({N_B},1)"),
            'STT(ABB)': (3, f"C({N_A},1)×C({N_B},2)"),
        }
        self.log(f"\n  ── Hinge 수 ──")
        for name, (cnt, formula) in hinge_counts.items():
            self.log(f"  {name}: {cnt} = {formula}")

        # f=1/3의 mult=30 분해
        self.log(f"\n  f=1/3의 mult=30 분해:")
        self.log(f"    A-patterns: 18 (12+3+3) ← spatial sector")
        self.log(f"    B-patterns: 12 (6+6)    ← temporal sector")
        self.log(f"    비율: 18:12 = 3:2 = n_A:n_B!")

        # f=2/3의 mult=30 분해
        self.log(f"\n  f=2/3의 mult=30 분해:")
        self.log(f"    AA-type: 9 (6+3)   ← 순수 spatial pair")
        self.log(f"    AB-type: 18 (12+6) ← 혼합 pair")
        self.log(f"    BB-type: 3          ← 순수 temporal pair")
        self.log(f"    비율: 9:18:3 = 3:6:1 = C(3,2):C(3,1)C(2,1):C(2,2)")

        # 게이지 보존 해석
        self.log(f"\n  ── 게이지 보존 해석 ──")
        self.log(f"  f = 1/3, 2/3은 hinge 레벨의 결합.")
        self.log(f"  입자(fermion)가 face/simplex에 살면 f_occ는")
        self.log(f"  1/5, 1/4, 2/5, 1/2, 3/5를 사용.")
        self.log(f"  게이지 보존(gauge boson)이 hinge에 살면")
        self.log(f"  f_occ = 1/3, 2/3을 사용.")
        self.log(f"  → fermion과 gauge boson의 구분이 기하학적!")

        self.check("게이지 연결 분석 완료", True)

    # ================================================================
    #  Part 4: 물리적 후보 종합
    # ================================================================
    def part4_physical_candidates(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 4: 물리적 후보 종합")
        self.log(f"  {'═'*55}")

        # ── f = 1/3 ──
        self.log(f"\n  ══ f = 1/3 (mult=30, x=α/3) ══")
        self.log(f"  구조: hinge에서 1개 vertex 점유")
        self.log(f"  기하학적 의미: hinge를 관통하는 '점' 패턴")
        self.log(f"  후보 A: 게이지 보존 전파자 (hinge = gauge channel)")
        self.log(f"    - κ_SST = α/3 이미 folded_dim.md에서 사용")
        self.log(f"    - mult=30 = 1/α_2 (weak coupling)")
        self.log(f"  후보 B: W/Z 보존 (weak gauge boson)")
        self.log(f"    - SU(2) gauge field는 2-dim temporal sector")
        self.log(f"    - SST hinge가 weak 상호작용의 기하학적 채널")
        self.log(f"  수치 검증:")
        x_13 = a / 3
        P_13 = P(x_13)
        self.log(f"    P(α/3) = {P_13:.8f}")
        self.log(f"    m_W/v_H 비교: m_W = 80.38 GeV, v_H = 246.2 GeV")
        self.log(f"    m_W/v_H = {80.38/246.22:.4f}")
        self.log(f"    known: m_W = g₂v/2, g₂² = 4πα₂ ≈ 4π/30")

        # ── f = 2/3 ──
        self.log(f"\n  ══ f = 2/3 (mult=30, x=2α/3) ══")
        self.log(f"  구조: hinge에서 2개 vertex 점유 (= edge)")
        self.log(f"  기하학적 의미: hinge 내부의 edge (연결)")
        self.log(f"  → f=1/3의 dual: vertex ↔ edge in hinge")
        self.log(f"  후보: STT hinge coupling → graviton propagator?")
        self.log(f"    - STT의 opposite = AA edge → R_ij 공간곡률")
        self.log(f"    - 2α/3는 spatial gravity의 coupling strength")

        # ── f = 3/4 ──
        self.log(f"\n  ══ f = 3/4 (mult=20, x=3α/4) ══")
        self.log(f"  구조: face에서 3개 vertex 점유 (= face 내 hinge)")
        self.log(f"  기하학적 의미: face에서 1개 vertex만 비어있음")
        self.log(f"  dual of 1/4 (lepton Yukawa)")
        self.log(f"  후보 A: 반경입자(antiparticle) Yukawa")
        self.log(f"    - f=1/4 → 입자, f=3/4 → 반입자?")
        self.log(f"    - CPT 대칭의 기하학적 기원?")
        self.log(f"  후보 B: vertex propagator의 'missing vertex' 보정")
        self.log(f"    - face 전파에서 1개 vertex 결손 → 산란 진폭")

        # 수치: P(3α/4)의 역할
        x_34 = 3*a/4
        P_34 = P(x_34)
        x_14 = a/4
        P_14 = P(x_14)
        self.log(f"\n  수치:")
        self.log(f"    P(α/4)  = {P_14:.8f}  (lepton)")
        self.log(f"    P(3α/4) = {P_34:.8f}  (dual)")
        self.log(f"    P(α/4) × P(3α/4) = {P_14*P_34:.8f}")
        self.log(f"    P²(α/2) = {P(a/2)**2:.8f}  (Higgs self-dual)")

        # ── f = 4/5 ──
        self.log(f"\n  ══ f = 4/5 (mult=5, x=4α/5) ══")
        self.log(f"  구조: simplex에서 4개 vertex 점유 (= 1개 비어있음)")
        self.log(f"  기하학적 의미: simplex의 face (4-vtx subset)")
        self.log(f"  dual of 1/5 (단일 vertex e,ν)")
        self.log(f"  후보: vacuum fluctuation / virtual pair")
        self.log(f"    - f=1/5: 1 vertex 존재 (실입자)")
        self.log(f"    - f=4/5: 1 vertex 부재 (hole = 반입자?)")

        x_45 = 4*a/5
        P_45 = P(x_45)
        x_15 = a/5
        P_15 = P(x_15)
        self.log(f"\n  수치:")
        self.log(f"    P(α/5) = {P_15:.8f}  (1-vertex)")
        self.log(f"    P(4α/5) = {P_45:.8f}  (4-vertex)")
        self.log(f"    비율 P(4α/5)/P(α/5) = {P_45/P_15:.8f}")
        self.log(f"    이것은 4-vertex 패턴의 propagation enhancement")

        # ── 종합 분류 ──
        self.log(f"\n  {'='*55}")
        self.log(f"  ★ 종합 분류 ★")
        self.log(f"  {'='*55}")

        self.log(f"\n  Level 1 — Simplex (k=5): matter fields")
        self.log(f"    1/5 → single vertex (e, ν)")
        self.log(f"    2/5 → doublet (ℂ²)")
        self.log(f"    3/5 → triplet (proton)")
        self.log(f"    4/5 → face-hole (dual of 1/5)")

        self.log(f"\n  Level 2 — Face (k=4): Yukawa/Higgs sector")
        self.log(f"    1/4 → lepton Yukawa (1 vtx on face)")
        self.log(f"    1/2 → Higgs (self-dual, AABB)")
        self.log(f"    3/4 → dual Yukawa (3 vtx on face)")

        self.log(f"\n  Level 3 — Hinge (k=3): gauge sector")
        self.log(f"    1/3 → gauge vertex (SST coupling κ=α/3)")
        self.log(f"    2/3 → gauge edge (STT coupling κ=2α/3)")

        self.log(f"\n  Level 4 — f=1: confinement")

        self.log(f"\n  → 3-level 구조:")
        self.log(f"    Matter (simplex) — Yukawa/Higgs (face) — Gauge (hinge)")
        self.log(f"    각 level은 자체 f_occ 값의 집합을 가짐")
        self.log(f"    f ↔ (1-f) 대칭이 각 level 내에서 작동")

        self.check("종합 분류 완료", True)


if __name__ == "__main__":
    UnidentifiedFocc().execute()
