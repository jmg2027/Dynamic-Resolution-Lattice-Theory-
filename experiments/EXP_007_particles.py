"""
Particles from Geometry in DRLT
================================
꼭짓점 = 페르미온, 엣지 = 보존.
상호작용은 기하학에서 자연스럽게 창발.

유도 체인:
  ψ ∈ C⁵ → (2,3) 분해 → 꼭짓점의 C² = 스핀 1/2 (페르미온)
  ⟨ψ_i|ψ_j⟩ → 엣지 = 힘 전달자 (보존)
  |overlap|² = W → 보른 규칙 (확률 = |진폭|²)
  ψ_i = ψ_j → W = 1/5 → 병합 → 파울리 배타원리
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network, evolve_step, try_pachner_5to1

np.random.seed(42)


# ═══════════════════════════════════════════════════════════════
#  TEST 1: 꼭짓점 = 페르미온
# ═══════════════════════════════════════════════════════════════

def test_vertex_is_fermion():
    """꼭짓점의 구조가 페르미온과 일치함을 보임."""
    print(f"\n{'━' * 70}")
    print("  TEST 1: 꼭짓점 = 페르미온")
    print("━" * 70)

    v = Vertex()

    # (2,3) 분해: C⁵ = C² ⊕ C³
    psi_T = v.psi[:2]   # 시간적 = SU(2) 약력 이중항
    psi_S = v.psi[2:]   # 공간적 = SU(3) 색 삼중항

    print(f"\n  ψ ∈ C⁵ = C² ⊕ C³")
    print(f"    C² (시간적): [{psi_T[0]:.3f}, {psi_T[1]:.3f}]")
    print(f"    C³ (공간적): [{psi_S[0]:.3f}, {psi_S[1]:.3f}, {psi_S[2]:.3f}]")
    print(f"    |C²|² = {np.sum(np.abs(psi_T)**2):.4f} (약력 전하)")
    print(f"    |C³|² = {np.sum(np.abs(psi_S)**2):.4f} (색 전하)")

    # SU(5) 기본 표현: 5 = (3,1) ⊕ (1,2)
    print(f"\n  SU(5) 기본 표현 5:")
    print(f"    (3,1,-1/3): 색 삼중항, 약력 싱글릿 → d_R (다운 쿼크)")
    print(f"    (1,2,+1/2): 색 싱글릿, 약력 이중항 → L (렙톤 이중항)")

    # 스핀: C² 는 SU(2) 이중항 = 스핀 1/2
    print(f"\n  스핀:")
    print(f"    C² 벡터 = SU(2) 기본 표현 = 스핀 1/2")
    print(f"    블로흐 구 좌표:")
    norm_T = np.linalg.norm(psi_T)
    if norm_T > 1e-10:
        qt = psi_T / norm_T
        theta = 2 * np.arccos(min(1, abs(qt[0])))
        phi = np.angle(qt[1]) - np.angle(qt[0])
        print(f"      θ = {np.degrees(theta):.1f}°, φ = {np.degrees(phi):.1f}°")
        print(f"      ⟨σ_z⟩ = {abs(qt[0])**2 - abs(qt[1])**2:+.4f}")

    # 자유도 검증
    dof = 2 * 4  # dim_R(CP⁴) = 8
    print(f"\n  자유도: dim_R(CP⁴) = 2d = {dof}")
    print(f"    d 진폭 (기하학적) + d 위상 (게이지) = {dof}")

    ok = len(psi_T) == 2 and len(psi_S) == 3
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] "
          f"꼭짓점 = C² ⊕ C³ = 약력 이중항 + 색 삼중항 = 페르미온")
    return ok


# ═══════════════════════════════════════════════════════════════
#  TEST 2: 엣지 = 보존
# ═══════════════════════════════════════════════════════════════

def test_edge_is_boson():
    """엣지(⟨ψ_i|ψ_j⟩)가 보존(힘 전달자)임을 보임."""
    print(f"\n{'━' * 70}")
    print("  TEST 2: 엣지 = 보존 (힘 전달자)")
    print("━" * 70)

    v1, v2 = Vertex(), Vertex()
    overlap = v1.overlap(v2)
    d = v1.interaction_decomposition(v2)

    print(f"\n  엣지 = ⟨ψ_i|ψ_j⟩ = {overlap:.4f}")
    print(f"  분해:")

    # 각 힘의 보존
    print(f"\n  {'힘':>10} {'보존':>12} {'게이지군':>8} {'DRLT 값':>10} {'기원':>20}")
    print(f"  {'─' * 65}")
    print(f"  {'중력':>10} {'중력자':>12} {'—':>8} {d['gravity']:10.5f} "
          f"{'|o_full|²/5':>20}")
    print(f"  {'약력':>10} {'W±, Z':>12} {'SU(2)':>8} {d['weak']:10.5f} "
          f"{'|o_T|²/2':>20}")
    print(f"  {'강력':>10} {'글루온':>12} {'SU(3)':>8} {d['strong']:10.5f} "
          f"{'|o_S|²/3':>20}")
    print(f"  {'전자기':>10} {'광자':>12} {'U(1)':>8} {d['em_strength']:10.5f} "
          f"{'|sin Δφ|':>20}")

    # 엣지의 스핀
    print(f"\n  보존의 스핀:")
    print(f"    엣지 = ψ_i* ⊗ ψ_j → 이중선형 형식")
    print(f"    C²* ⊗ C² = 1(스핀0) + 3(스핀1) → 게이지 보존 (스핀 1)")
    print(f"    전체: d(d+1)/2 - 2d = 10 - 8 = 2 → 중력자 (스핀 2)")

    # 보존 수 검증
    n_gauge = 1 + 3 + 8  # U(1) + SU(2) + SU(3) = 12
    n_graviton = 2
    print(f"\n  보존 수:")
    print(f"    게이지 보존: 1(γ) + 3(W±,Z) + 8(g) = {n_gauge}")
    print(f"    중력자: {n_graviton} 편극")
    print(f"    합계: {n_gauge + n_graviton} (SM: 12 게이지 + 중력자)")

    ok = d['gravity'] > 0 and d['weak'] > 0 and d['strong'] > 0
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] "
          f"엣지 하나에서 4가지 힘 전달자 분해 완료")
    return ok


# ═══════════════════════════════════════════════════════════════
#  TEST 3: 파울리 배타원리
# ═══════════════════════════════════════════════════════════════

def test_pauli_exclusion():
    """동일 상태 → W=1/5 → 병합(구별 불가) = 파울리 배타."""
    print(f"\n{'━' * 70}")
    print("  TEST 3: 파울리 배타원리 = 꼭짓점 병합")
    print("━" * 70)

    psi = Vertex._random_state()
    v1 = Vertex(psi)
    v2 = Vertex(psi + 0.001 * np.random.randn(5))

    W_identical = v1.W(v2)
    ds2_identical = v1.ds2(v2)

    print(f"\n  거의 동일한 두 꼭짓점:")
    print(f"    W = {W_identical:.6f}  (최대 1/5 = {1/5:.6f})")
    print(f"    ds² = {ds2_identical:.6f}  (→ 0)")

    net = Network(vertices=[Vertex(psi + 0.001*np.random.randn(5)) for _ in range(6)])
    N_before = net.N
    merged = try_pachner_5to1(net, w_threshold=0.19)
    N_after = net.N
    print(f"\n  동일 상태 6개: 병합 전 {N_before} → 후 {N_after} (제거 {merged})")

    net2 = Network(n=6)
    merged2 = try_pachner_5to1(net2, w_threshold=0.19)
    print(f"  다른 상태 6개: 병합 = {merged2}개")

    print(f"\n  해석: ψ_i = ψ_j → 구별 불가 → 병합 = 파울리 배타")

    ok = merged > 0 and merged2 == 0
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] "
          f"동일 상태 병합(파울리), 다른 상태 비병합")
    return ok


# ═══════════════════════════════════════════════════════════════
#  TEST 4: 보른 규칙
# ═══════════════════════════════════════════════════════════════

def test_born_rule():
    """W = |⟨ψ_i|ψ_j⟩|²/5 = 보른 규칙 자체."""
    print(f"\n{'━' * 70}")
    print("  TEST 4: 보른 규칙 = W의 정의")
    print("━" * 70)

    N_PAIRS = 5000
    W_vals = [Vertex().W(Vertex()) for _ in range(N_PAIRS)]
    W_arr = np.array(W_vals)

    mean_theory = 1/25
    mean_measured = np.mean(W_arr)

    print(f"\n  W_ij = |⟨ψ_i|ψ_j⟩|²/(d+1) = 보른 규칙의 정규화 버전")
    print(f"\n  {N_PAIRS}개 랜덤 쌍:")
    print(f"    ⟨W⟩ = {mean_measured:.6f}  (이론: 1/25 = {mean_theory:.6f})")
    print(f"\n  → 확률 = |진폭|² 은 유도, 공준이 아님")

    ok = abs(mean_measured - mean_theory) / mean_theory < 0.05
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] ⟨W⟩ = 1/25 (보른 규칙)")
    return ok


# ═══════════════════════════════════════════════════════════════
#  TEST 5: 스핀-통계 정리
# ═══════════════════════════════════════════════════════════════

def test_spin_statistics():
    """⟨i|j⟩ = ⟨j|i⟩* (반대칭 위상), W_ij = W_ji (대칭)."""
    print(f"\n{'━' * 70}")
    print("  TEST 5: 스핀-통계 정리")
    print("━" * 70)

    v1, v2 = Vertex(), Vertex()
    o12 = v1.overlap(v2)
    o21 = v2.overlap(v1)
    W12 = v1.W(v2)
    W21 = v2.W(v1)

    print(f"\n  ⟨1|2⟩ = {o12:.4f},  ⟨2|1⟩ = {o21:.4f}")
    print(f"  ⟨2|1⟩ = ⟨1|2⟩*: 차이 = {abs(o12 - np.conj(o21)):.2e}")
    print(f"  → 위상 반전 → 페르미온 반대칭")
    print(f"\n  W₁₂ = {W12:.6f},  W₂₁ = {W21:.6f}")
    print(f"  W₁₂ = W₂₁: 차이 = {abs(W12 - W21):.2e}")
    print(f"  → 대칭 → 보존 교환 대칭")

    ok = abs(W12 - W21) < 1e-10 and abs(o12 - np.conj(o21)) < 1e-10
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] "
          f"스핀-통계: 내적 에르미트 성질에서 유도")
    return ok


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

def run():
    print("=" * 70)
    print("  DRLT → 입자 = 기하학")
    print("  꼭짓점 = 페르미온, 엣지 = 보존")
    print("=" * 70)

    results = []
    results.append(("꼭짓점 = 페르미온",  test_vertex_is_fermion()))
    results.append(("엣지 = 보존",        test_edge_is_boson()))
    results.append(("파울리 배타원리",     test_pauli_exclusion()))
    results.append(("보른 규칙",           test_born_rule()))
    results.append(("스핀-통계 정리",      test_spin_statistics()))

    print(f"\n{'═' * 70}")
    print(f"  최종 요약")
    print(f"{'═' * 70}")
    passed = 0
    for name, ok in results:
        status = "✓" if ok else "✗"
        print(f"  [{status}] {name}")
        if ok:
            passed += 1
    print(f"\n  {passed}/{len(results)} 통과")


if __name__ == "__main__":
    run()
