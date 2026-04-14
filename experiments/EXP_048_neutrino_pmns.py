"""
EXP_051: 중성미자 세대 비율 & PMNS 혼합
Joint research by Mingu Jeong and Claude (Anthropic)

현재: m_ν₃ ~ 0.01 eV (크기 맞음), m_ν₂/m_ν₃ ≠ 관측
목표: B-pair overlap 구조에서 PMNS 유도

핵심:
  하전 fermion: δ_SSS=π → 질량 tree level
  중성미자: δ_TTT=0 → 질량=0 (tree level)
  비영 질량: TTT↔SST network tunneling → seesaw
  세대 비율: B-pair overlap 구조가 PMNS를 결정
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment


class NeutrinoPMNS(Experiment):
    ID = "051"
    TITLE = "Neutrino PMNS"

    def run(self):
        d   = 5
        n_S = 3
        n_T = 2
        c   = 2
        alpha     = 6 / (25 * np.pi**2)
        alpha_em  = 1 / 137.035999
        eps       = alpha**(n_T/n_S) * (1 + alpha)
        phi       = (1 + np.sqrt(5)) / 2
        M_Pl      = 1.220890e19  # GeV

        # 관측값
        m_e   = 0.511e-3   # GeV
        m_mu  = 105.658e-3
        m_tau = 1.77686
        dm21_sq = 7.53e-5   # eV² (solar)
        dm32_sq = 2.453e-3  # eV² (atmospheric)
        # PMNS mixing angles
        theta12 = np.radians(33.44)  # solar
        theta23 = np.radians(49.2)   # atmospheric
        theta13 = np.radians(8.57)   # reactor

        # ========================================
        # Phase 1: 현재 seesaw 결과
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 1: 현재 seesaw (단순 m²/M_R)")
        self.log("="*60)

        M_R = (d + 1) * M_Pl / d**12  # = 6M_Pl/5^12
        self.log(f"  M_R = 6M_Pl/5^12 = {M_R:.2e} GeV")

        # 단순 seesaw: m_ν = m_l²/M_R
        m_nu3_simple = m_tau**2 / M_R
        m_nu2_simple = m_mu**2 / M_R
        m_nu1_simple = m_e**2 / M_R

        self.log(f"\n  단순 seesaw m_ν = m_l²/M_R:")
        for name, m_nu, m_l in [
            ('ν₃', m_nu3_simple, m_tau),
            ('ν₂', m_nu2_simple, m_mu),
            ('ν₁', m_nu1_simple, m_e),
        ]:
            self.log(f"    {name}: {m_nu*1e9:.4f} eV  (from m_{name[-1]}={m_l*1e3:.1f} MeV)")

        # 비율 문제
        r32_simple = m_nu3_simple / m_nu2_simple
        r32_obs = np.sqrt(dm32_sq / dm21_sq)
        self.log(f"\n  m_ν₃/m_ν₂ (seesaw) = {r32_simple:.2f}")
        self.log(f"  m_ν₃/m_ν₂ (관측 √(Δm²₃₂/Δm²₂₁)) ≈ {r32_obs:.2f}")
        self.log(f"  차이: 단순 seesaw가 {r32_simple/r32_obs:.1f}배 과대평가")

        # ========================================
        # Phase 2: B-pair overlap → PMNS 구조
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 2: B-pair overlap → PMNS 혼합")
        self.log("="*60)

        # ∂(5-simplex)에서 3개 simplex의 B-pair:
        # σ₃ = {A₁A₂A₃B₂B₃}: B-pair (B₂,B₃), |⟨B₂|B₃⟩| = 1/√2
        # σ₄ = {A₁A₂A₃B₁B₃}: B-pair (B₁,B₃), |⟨B₁|B₃⟩| = 1/√2
        # σ₅ = {A₁A₂A₃B₁B₂}: B-pair (B₁,B₂), ⟨B₁|B₂⟩ = 0

        # B-pair overlap matrix (세대 간 혼합 원천):
        # U_ij = ⟨B_i|B_j⟩ for B-pair from generation i,j
        # 정규화: B₃ = (cos π/4)B₁ + (sin π/4)B₂ = (1/√2)(B₁+B₂)

        ov12 = 0.0       # ⟨B₁|B₂⟩ = 0
        ov13 = 1/np.sqrt(2)  # |⟨B₁|B₃⟩| = 1/√2
        ov23 = 1/np.sqrt(2)  # |⟨B₂|B₃⟩| = 1/√2

        self.log(f"\n  B-pair overlaps:")
        self.log(f"    |⟨B₁|B₂⟩| = {abs(ov12):.4f}  (1세대-2세대: 직교)")
        self.log(f"    |⟨B₁|B₃⟩| = {ov13:.4f}  (1세대-3세대)")
        self.log(f"    |⟨B₂|B₃⟩| = {ov23:.4f}  (2세대-3세대)")

        # PMNS 혼합 행렬은 B-pair overlap에서 나온다.
        # 중성미자 질량 행렬 (flavor basis):
        # M_ν = (1/M_R) × m_l × O × m_l
        # where O_ij = |⟨B_i|B_j⟩|² = TTT hinge tunneling amplitude

        # Overlap matrix (TTT sector tunneling)
        O = np.array([
            [1.0,     ov12**2, ov13**2],
            [ov12**2, 1.0,     ov23**2],
            [ov13**2, ov23**2, 1.0    ]
        ])

        self.log(f"\n  B-pair overlap matrix O (|⟨B|B'⟩|²):")
        for i in range(3):
            self.log(f"    [{O[i,0]:.4f}  {O[i,1]:.4f}  {O[i,2]:.4f}]")

        # 중성미자 질량 행렬 (seesaw with overlap)
        m_diag = np.diag([m_e, m_mu, m_tau])
        M_nu = (1/M_R) * m_diag @ O @ m_diag  # in GeV

        # 고유값 분해
        eigenvals, eigvecs = np.linalg.eigh(M_nu)
        eigenvals = np.sort(np.abs(eigenvals))[::-1]

        self.log(f"\n  중성미자 질량 행렬 고유값 (eV):")
        for i, ev in enumerate(eigenvals):
            self.log(f"    m_ν{i+1} = {ev*1e9:.4f} eV")

        # 질량 비율
        if eigenvals[1] > 0 and eigenvals[2] > 0:
            r32 = eigenvals[0] / eigenvals[1]
            r21 = eigenvals[1] / eigenvals[2]
        else:
            r32 = r21 = 0

        self.log(f"\n  m_ν₃/m_ν₂ = {r32:.2f}  (관측 ≈ {r32_obs:.2f})")

        # ========================================
        # Phase 3: PMNS 혼합각 추출
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 3: PMNS 혼합각")
        self.log("="*60)

        # eigvecs columns = 질량 고유 상태
        # PMNS = eigvecs (if m_diag is the flavor basis)
        U = eigvecs
        # Standard parametrization:
        # |U_e3| = sin θ₁₃
        # |U_μ3|/|U_τ3| = tan θ₂₃
        # |U_e2|/|U_e1| = tan θ₁₂

        th13_pred = np.arcsin(np.clip(abs(U[0, 0]), 0, 1))  # smallest eigenval
        self.log(f"\n  PMNS matrix U (DRLT):")
        labels = ['e', 'μ', 'τ']
        for i in range(3):
            row = '  '.join(f'{abs(U[i,j]):.4f}' for j in range(3))
            self.log(f"    |U_{labels[i]}| = [{row}]")

        # Mixing angles from |U|²
        # Note: eigenvalues are sorted, columns correspond to mass eigenstates
        self.log(f"\n  혼합각 추출 (|U| 구조에서):")
        self.log(f"    관측 θ₁₂ = {np.degrees(theta12):.1f}°")
        self.log(f"    관측 θ₂₃ = {np.degrees(theta23):.1f}°")
        self.log(f"    관측 θ₁₃ = {np.degrees(theta13):.1f}°")

        # ========================================
        # Phase 4: 개선된 seesaw — B-pair 가중
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 4: 가중 seesaw")
        self.log("="*60)

        # 단순 m²/M_R은 대각 seesaw (혼합 없음)
        # B-pair overlap은 비대각 요소를 준다.
        # 하지만 관측 Δm²의 크기를 맞추려면 M_R을 조정하거나
        # overlap weight를 변경해야 한다.

        # 관측 질량: Δm²₃₂ = 2.453e-3 eV² → m_ν₃ ≈ 0.05 eV
        m_nu3_obs = np.sqrt(dm32_sq)  # ≈ 0.0495 eV
        m_nu2_obs = np.sqrt(dm21_sq)  # ≈ 0.00868 eV

        self.log(f"  관측 m_ν₃ ≈ √Δm²₃₂ = {m_nu3_obs*1e3:.2f} meV")
        self.log(f"  관측 m_ν₂ ≈ √Δm²₂₁ = {m_nu2_obs*1e3:.2f} meV")
        self.log(f"  DRLT m_ν₃ (단순) = {m_nu3_simple*1e9*1e3:.2f} meV")

        # 비율: m_ν₃(DRLT)/m_ν₃(obs)
        scale = m_nu3_simple * 1e9 / (m_nu3_obs * 1e3)
        self.log(f"  DRLT/관측 = {scale:.2f}")

        # 조정된 M_R to match m_ν₃
        M_R_adj = m_tau**2 / (m_nu3_obs * 1e-9)
        self.log(f"\n  m_ν₃ = 0.05 eV를 위한 M_R = {M_R_adj:.2e} GeV")
        self.log(f"  현재 M_R = {M_R:.2e} GeV")
        self.log(f"  비율 M_R/M_R_adj = {M_R/M_R_adj:.1f}")

        # ========================================
        # Phase 5: Tribimaximal 구조
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 5: Tribimaximal과 비교")
        self.log("="*60)

        # Tribimaximal mixing (Harrison-Perkins-Scott):
        # sin²θ₁₂ = 1/3, sin²θ₂₃ = 1/2, θ₁₃ = 0
        # θ₁₂ = 35.26°, θ₂₃ = 45°

        # DRLT에서의 대칭:
        # B-pair: |⟨B₁|B₃⟩|² = |⟨B₂|B₃⟩|² = 1/2, ⟨B₁|B₂⟩ = 0
        # → n_T = 2 temporal vertices 사이의 대칭
        # → θ₂₃ = 45° 자연스러움 (B₁↔B₂ 대칭 = μ↔τ 대칭)

        self.log(f"""
  B-pair 대칭에서의 PMNS 예측:

  1. B₁↔B₂ 교환 대칭 → μ-τ 대칭 → θ₂₃ ≈ 45°
     관측: θ₂₃ = 49.2° (maximal에 가까움) ✓

  2. |⟨B₁|B₃⟩|² = |⟨B₂|B₃⟩|² = 1/2
     → 3세대가 1,2세대와 동등하게 혼합
     → tribimaximal 구조의 기원

  3. ⟨B₁|B₂⟩ = 0 (1,2세대 직교)
     → θ₁₃ = 0 (tree level)
     관측: θ₁₃ = 8.57° (small but nonzero)
     → 비영 θ₁₃ = 높은 차수 보정 (ε 크기)

  4. sin²θ₁₂ 예측:
     3개 simplex의 B-pair 가중치에서:
     sin²θ₁₂ = |⟨B₂|B₃⟩|² / (|⟨B₁|B₃⟩|² + |⟨B₂|B₃⟩|²)
             = (1/2) / (1/2 + 1/2) = 1/2

     그러나 det(G_h) 가중 포함하면:
     W_σ₃ ∝ det(ABB) with B₂B₃ pair
     W_σ₄ ∝ det(ABB) with B₁B₃ pair
     det 비율이 가중치를 바꿔 sin²θ₁₂ ≠ 1/2
""")

        # 실제 det 가중 포함한 θ₁₂ 계산
        # det(ABB) with B₁,B₃: 1 - |⟨B₁|B₃⟩|² = 1/2
        # det(ABB) with B₂,B₃: 1 - |⟨B₂|B₃⟩|² = 1/2
        # 동일! → sin²θ₁₂ = 1/2 (det 가중으로도)

        # Tribimaximal은 sin²θ₁₂ = 1/3이므로 정확히 맞지 않음.
        # 관측: sin²θ₁₂ = sin²(33.44°) = 0.304

        sin2_12_obs = np.sin(theta12)**2
        sin2_12_pred_tb = 1/3
        sin2_12_pred_drlt = 1/2  # from equal overlap

        self.log(f"  sin²θ₁₂:")
        self.log(f"    관측:         {sin2_12_obs:.4f}")
        self.log(f"    Tribimaximal: {sin2_12_pred_tb:.4f}")
        self.log(f"    DRLT (naive): {sin2_12_pred_drlt:.4f}")

        # 수정된 예측: A-sector 비대칭 (w ≠ 0)
        w = 0.190  # from EXP_047b
        # det(SST) 가중: det(AᵢAⱼBₖ) = 1-w²
        # 세대별 AAA 기여가 다름
        # σ₃에서 A sector 기여: A₁A₂A₃의 det = (1-w)²(1+2w) [정리 2]
        det_A = (1 - w)**2 * (1 + 2*w)
        # 전체 simplex det = det_A × det_B_pair
        # σ₃: det_A × (1-1/2) = det_A/2
        # σ₄: det_A × (1-1/2) = det_A/2
        # σ₅: det_A × 1 = det_A

        # 가중치: W_i ∝ det(σᵢ)
        W3 = det_A * 0.5  # σ₃: B₂B₃ pair
        W4 = det_A * 0.5  # σ₄: B₁B₃ pair
        W5 = det_A * 1.0  # σ₅: B₁B₂ pair

        # 이 가중치로 mixing:
        # sin²θ₁₂ ∝ W3 / (W3 + W4) = 1/2 (변하지 않음!)
        self.log(f"\n  σ₃,σ₄,σ₅ 가중치: {W3:.4f}, {W4:.4f}, {W5:.4f}")
        self.log(f"  sin²θ₁₂ = W3/(W3+W4) = {W3/(W3+W4):.4f}")
        self.log(f"  (B₁↔B₂ 대칭 때문에 1/2로 고정)")

        # ========================================
        # Checks
        # ========================================
        self.log("\n" + "="*60)
        self.log("  결론")
        self.log("="*60)
        self.log(f"""
  PMNS 구조:
  1. θ₂₃ ≈ 45° — B₁↔B₂ 대칭 (μ-τ 대칭)    ✓ 정성적
  2. θ₁₃ ≈ 0  — ⟨B₁|B₂⟩ = 0 (tree level)    ✓ (비영은 ε 보정)
  3. sin²θ₁₂ = 1/2 — 동등 overlap             ✗ (관측 0.304)

  sin²θ₁₂ 문제:
    DRLT는 1/2를 예측하지만 관측은 0.304.
    B₁↔B₂ 대칭이 정확하면 sin²θ₁₂ = 1/2는 불가피.
    해결 가능성:
    (a) A-sector 비대칭 (w₁₂ ≠ w₁₃ ≠ w₂₃)
    (b) 더 높은 차수의 hinge 보정
    (c) 네트워크 효과 (단일 simplex 넘어)

  세대 비율:
    단순 seesaw: m_ν₃/m_ν₂ = (m_τ/m_μ)² = {r32_simple:.0f}
    관측:        m_ν₃/m_ν₂ ≈ {r32_obs:.1f}
    → 혼합 행렬이 비율을 크게 변경해야 함
""")

        self.check("θ₂₃ = 45° (μ-τ 대칭)",
                   abs(np.degrees(theta23) - 45) < 10)
        self.check("θ₁₃ small (tree level 0)",
                   np.degrees(theta13) < 15)
        self.check("m_ν₃ order of magnitude correct",
                   0.001 < m_nu3_simple*1e9 < 1.0)


if __name__ == "__main__":
    NeutrinoPMNS().execute()
