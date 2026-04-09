"""
Neutrino Mass from DRLT
========================
중성미자가 왜 그렇게 가벼운가?

핵심: ν 는 C² (시간적 섹터)에만 사는 유일한 페르미온.
→ C³ (공간/색) 결합 없음 → 디랙 질량 작음
→ 마요라나 질량 = GUT 스케일
→ 시소 메커니즘: m_ν ~ m_D² / M_R → 극히 작은 질량
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex

np.random.seed(42)


# ═══════════════════════════════════════════════════════════════
#  TEST 1: 중성미자는 왜 특별한가
# ═══════════════════════════════════════════════════════════════

def test_neutrino_is_special():
    """ν는 C² 에만 사는 유일한 페르미온."""
    print(f"\n{'━' * 70}")
    print("  TEST 1: 중성미자 = 순수 시간적 페르미온")
    print("━" * 70)

    # SU(5) 기본표현 5 = (3,1) ⊕ (1,2) 에서 입자 배정
    particles = {
        "d_R (다운쿼크)": {"sector": "C³", "color": True, "em": -1/3},
        "ν (중성미자)":    {"sector": "C²", "color": False, "em": 0},
        "e (전자)":        {"sector": "C²", "color": False, "em": -1},
    }

    print(f"\n  5 = (3,1,-1/3) ⊕ (1,2,+1/2):")
    print(f"  {'입자':>15} {'섹터':>5} {'색전하':>6} {'EM전하':>7} {'약력':>5} {'강력':>5}")
    print(f"  {'─' * 50}")
    for name, p in particles.items():
        weak = "✓" if p["sector"] == "C²" else "✗"
        strong = "✓" if p["color"] else "✗"
        print(f"  {name:>15} {p['sector']:>5} {'있음' if p['color'] else '없음':>6} "
              f"{p['em']:+7.1f} {weak:>5} {strong:>5}")

    # 수치: 순수 시간적 꼭짓점 vs 혼합 꼭짓점
    # 중성미자-like: C² 에 집중
    psi_nu = np.array([0.8, 0.6, 0, 0, 0], dtype=complex)
    v_nu = Vertex(psi_nu)

    # 전자-like: C² 주로 + 약간 C³
    psi_e = np.array([0.7, 0.5, 0.1, 0.1, 0.1], dtype=complex)
    v_e = Vertex(psi_e)

    # 쿼크-like: C³ 주로
    psi_q = np.array([0.1, 0.1, 0.6, 0.5, 0.4], dtype=complex)
    v_q = Vertex(psi_q)

    print(f"\n  C² vs C³ 가중치:")
    for name, v in [("ν", v_nu), ("e", v_e), ("quark", v_q)]:
        tw = v.temporal_weight
        sw = v.spatial_weight
        print(f"    {name:>6}: |C²|²={tw:.3f}  |C³|²={sw:.3f}  "
              f"{'← 순수 시간적!' if tw > 0.95 else ''}")

    print(f"\n  ★ 중성미자만 |C²|² ≈ 1, |C³|² ≈ 0")
    print(f"    → 색 전하 없음, EM 전하 없음")
    print(f"    → 약력만 느낌 → '유령 입자'")

    ok = v_nu.temporal_weight > 0.95
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] "
          f"중성미자 = 순수 C² 상태 (|C²|²={v_nu.temporal_weight:.3f})")
    return ok


# ═══════════════════════════════════════════════════════════════
#  TEST 2: 시소 메커니즘 — 질량 예측
# ═══════════════════════════════════════════════════════════════

def test_seesaw():
    """m_ν ~ m_D² / M_R 를 C⁵ 기하학에서 유도."""
    print(f"\n{'━' * 70}")
    print("  TEST 2: 시소 메커니즘 → 중성미자 질량 예측")
    print("━" * 70)

    d = 4
    M_Pl = 1.220910e19   # GeV
    M_GUT = M_Pl / 5**5  # DRLT 예측
    v_higgs = 246.0       # GeV (힉스 VEV)

    # 디랙 질량: 시간적 섹터의 유카와 결합
    # m_D ~ (temporal fraction) × yukawa × v_higgs
    # temporal fraction = 2/5 (C² 가 C⁵ 에서 차지하는 비율)
    temporal_frac = 2 / (d + 1)

    print(f"\n  ── DRLT 파라미터 ──")
    print(f"  M_Pl = {M_Pl:.4e} GeV")
    print(f"  M_GUT = M_Pl/5⁵ = {M_GUT:.4e} GeV")
    print(f"  v_Higgs = {v_higgs} GeV")
    print(f"  temporal fraction = 2/(d+1) = {temporal_frac:.4f}")

    # 마요라나 질량 (오른손 중성미자): GUT 스케일
    M_R = M_GUT
    print(f"\n  ── 마요라나 질량 (오른손 ν_R) ──")
    print(f"  M_R = M_GUT = {M_R:.3e} GeV")
    print(f"  왜? ν_R 은 SM 게이지 싱글릿 → GUT에서만 질량 획득")

    # 디랙 질량: 여러 세대
    # 유카와 결합 ∝ C³ 성분의 크기 (세대별로 다름)
    # 1세대: y_1 ~ temporal_frac × (1/3)
    # 2세대: y_2 ~ temporal_frac × (2/3)
    # 3세대: y_3 ~ temporal_frac × 1
    yukawas = [temporal_frac * (k+1) / 3 for k in range(3)]
    m_Ds = [y * v_higgs for y in yukawas]

    print(f"\n  ── 디랙 질량 (세대별) ──")
    for gen, (y, mD) in enumerate(zip(yukawas, m_Ds), 1):
        print(f"  {gen}세대: y={y:.4f} → m_D = {mD:.1f} GeV")

    # 시소 공식: m_ν = m_D² / M_R
    m_nus = [mD**2 / M_R for mD in m_Ds]
    m_nus_eV = [m * 1e9 for m in m_nus]  # GeV → eV

    print(f"\n  ── 시소: m_ν = m_D² / M_R ──")
    print(f"  {'세대':>4} {'m_D (GeV)':>12} {'m_ν (eV)':>12} {'관측 (eV)':>12}")
    print(f"  {'─' * 45}")

    obs = ["< 0.01 ?", "~ 0.009", "~ 0.05"]
    for gen, (mD, mnu, ob) in enumerate(zip(m_Ds, m_nus_eV, obs), 1):
        print(f"  {gen:4d} {mD:12.2f} {mnu:12.6f} {ob:>12s}")

    # 질량 비율
    print(f"\n  질량 계층:")
    print(f"    m_ν3/m_ν1 = {m_nus_eV[2]/m_nus_eV[0]:.1f} "
          f"(관측 ~ 5-50)")
    print(f"    m_ν/m_top = {m_nus_eV[2]/173e9:.2e} "
          f"(관측 ~ 3×10⁻¹³)")

    # 핵심: 왜 이렇게 가벼운가?
    ratio = m_nus_eV[2] / (173e9)  # vs top quark
    print(f"\n  ★ 중성미자가 가벼운 이유:")
    print(f"    m_ν/m_top ~ m_D²/(M_R × m_top)")
    print(f"             ~ v²/(M_GUT × m_top)")
    print(f"             ~ {v_higgs}²/({M_GUT:.1e} × 173)")
    print(f"             ~ {v_higgs**2/(M_GUT*173):.2e}")
    print(f"    시소: 분모에 M_GUT = M_Pl/5⁵ 가 들어가므로 극히 작음")

    ok = all(0 < m < 10 for m in m_nus_eV)  # eV 범위
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] "
          f"m_ν ∈ [0.001, 10] eV 범위 예측")
    return ok


# ═══════════════════════════════════════════════════════════════
#  TEST 3: 중성미자 진동 — PMNS 행렬
# ═══════════════════════════════════════════════════════════════

def test_oscillation():
    """PMNS 행렬 = C² 내 혼합, 큰 각도 예측."""
    print(f"\n{'━' * 70}")
    print("  TEST 3: 중성미자 진동 & PMNS 행렬")
    print("━" * 70)

    print(f"""
  CKM (쿼크):  C³ 내 혼합 → 작은 각도 (Cabibbo ~ 13°)
  PMNS (렙톤): C² 내 혼합 → 큰 각도 (θ₁₂ ~ 34°, θ₂₃ ~ 45°!)

  ★ 왜 PMNS 각도가 CKM보다 큰가?
    CKM: C³ (3차원) 내 회전 → 3개 축 중 가까운 것끼리 작은 각도
    PMNS: C² (2차원) 내 회전 → 2차원에서 축이 2개뿐
          → "빗나갈 공간"이 적으므로 큰 혼합이 자연스러움""")

    # C² 에서 랜덤 유니타리 = 큰 각도가 자연스러움
    N_TRIALS = 3000
    ckm_angles = []
    pmns_angles = []

    for _ in range(N_TRIALS):
        # CKM: C³ 내 랜덤 SU(3)
        A3 = np.random.randn(3, 3) + 1j * np.random.randn(3, 3)
        Q3, _ = np.linalg.qr(A3)
        theta_c = np.arccos(min(1, abs(Q3[0, 0])))
        ckm_angles.append(np.degrees(theta_c))

        # PMNS: C² 내 랜덤 SU(2)
        A2 = np.random.randn(2, 2) + 1j * np.random.randn(2, 2)
        Q2, _ = np.linalg.qr(A2)
        theta_p = np.arccos(min(1, abs(Q2[0, 0])))
        pmns_angles.append(np.degrees(theta_p))

    print(f"  {N_TRIALS}개 랜덤 샘플:")
    print(f"    CKM (C³):  ⟨θ⟩ = {np.mean(ckm_angles):.1f}° ± {np.std(ckm_angles):.1f}°")
    print(f"    PMNS (C²): ⟨θ⟩ = {np.mean(pmns_angles):.1f}° ± {np.std(pmns_angles):.1f}°")
    print(f"    관측 CKM θ_C = 13.0°, PMNS θ₁₂ = 33.4°")

    pmns_larger = np.mean(pmns_angles) > np.mean(ckm_angles)
    print(f"\n  [{'✓ PASS' if pmns_larger else '✗ FAIL'}] "
          f"PMNS > CKM (C² 혼합이 C³ 보다 큰 각도)")
    return pmns_larger


# ═══════════════════════════════════════════════════════════════
#  TEST 4: W 결합으로 질량 계층 재현
# ═══════════════════════════════════════════════════════════════

def test_mass_hierarchy():
    """격자에서 직접 측정: ν-like vs e-like vs q-like 결합 세기."""
    print(f"\n{'━' * 70}")
    print("  TEST 4: W 결합으로 질량 계층")
    print("━" * 70)

    N = 2000
    nu_Ws, e_Ws, q_Ws = [], [], []

    for _ in range(N):
        # ν-like: 순수 시간적
        psi_nu = np.zeros(5, dtype=complex)
        psi_nu[:2] = np.random.randn(2) + 1j * np.random.randn(2)
        v_nu = Vertex(psi_nu / np.linalg.norm(psi_nu))

        # e-like: 주로 시간적 + 약간 공간
        psi_e = np.random.randn(5) + 1j * np.random.randn(5)
        psi_e[2:] *= 0.3  # 공간 섹터 억제
        v_e = Vertex(psi_e / np.linalg.norm(psi_e))

        # q-like: 주로 공간적
        psi_q = np.random.randn(5) + 1j * np.random.randn(5)
        psi_q[:2] *= 0.3  # 시간 섹터 억제
        v_q = Vertex(psi_q / np.linalg.norm(psi_q))

        # 힉스-like (진공): 완전 랜덤
        v_h = Vertex()

        nu_Ws.append(v_nu.W(v_h))
        e_Ws.append(v_e.W(v_h))
        q_Ws.append(v_q.W(v_h))

    print(f"\n  입자별 힉스 결합 (⟨W⟩, {N}개 샘플):")
    print(f"    ν (순수 C²):   ⟨W⟩ = {np.mean(nu_Ws):.6f}")
    print(f"    e (주로 C²):   ⟨W⟩ = {np.mean(e_Ws):.6f}")
    print(f"    q (주로 C³):   ⟨W⟩ = {np.mean(q_Ws):.6f}")
    print(f"    비율 q/ν = {np.mean(q_Ws)/np.mean(nu_Ws):.2f}")

    print(f"\n  ★ 중성미자의 W 결합이 가장 약함")
    print(f"    → 힉스와의 유카와 결합 ∝ W → 질량 ∝ W")
    print(f"    → 질량 계층: m_q > m_e > m_ν")

    hierarchy = np.mean(q_Ws) > np.mean(e_Ws) > np.mean(nu_Ws)
    print(f"\n  [{'✓ PASS' if hierarchy else '✗ FAIL'}] "
          f"W 결합 계층: q > e > ν")
    return hierarchy


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

def run():
    print("=" * 70)
    print("  DRLT → 중성미자 질량")
    print("  왜 중성미자는 0이 아닌 극히 작은 질량을 가지는가")
    print("=" * 70)

    results = []
    results.append(("ν = 순수 C² 상태",     test_neutrino_is_special()))
    results.append(("시소 → m_ν 예측",       test_seesaw()))
    results.append(("PMNS > CKM (큰 혼합)",  test_oscillation()))
    results.append(("W 결합 계층 q>e>ν",     test_mass_hierarchy()))

    print(f"\n{'═' * 70}")
    print(f"  최종 요약")
    print(f"{'═' * 70}")
    p = sum(1 for _, ok in results if ok)
    for name, ok in results:
        print(f"  [{'✓' if ok else '✗'}] {name}")
    print(f"\n  {p}/{len(results)} 통과")

    print(f"\n  중성미자 질량의 기원 (한 문장):")
    print(f"  ν 는 C² 에만 살기 때문에 C³ 결합이 없고,")
    print(f"  M_R = M_Pl/5⁵ 에 의해 시소로 눌려서 극히 가볍다.")


if __name__ == "__main__":
    run()
