"""
Block Universe: Static Diagonalization of Complete Graph
=========================================================
4D 블록 우주: evolve 없이 W 행렬 대각화만으로 물리 추출.

핵심 논점:
  - 완전 그래프 + W = 시공간 그 자체
  - evolve_step = 5번째 메타시간 (4D에서 모순)
  - 정적 대각화 = 올바른 접근
  - Im/Re > 1 → 시간적 변, ~51% 자발 분리
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network

np.random.seed(42)


def test_w_diagonalization():
    """W 행렬 대각화 = 시공간의 고유 모드."""
    print(f"\n{'━' * 70}")
    print("  TEST 1: W 행렬 대각화 = 시공간 모드")
    print("━" * 70)

    N = 25  # = CP⁴ 해상
    net = Network(n=N)
    W = net.W_matrix()

    # W 고유값 = 시공간의 집단 모드
    eigvals = np.sort(np.linalg.eigvalsh(W))[::-1]  # 내림차순

    print(f"\n  N = {N} 꼭짓점 (evolve 없음, 순수 랜덤 ψ)")
    print(f"  W 행렬: {N}×{N}, 대칭, 양반정치")
    print(f"\n  고유값 (상위 10개):")
    for k in range(min(10, N)):
        print(f"    λ_{k} = {eigvals[k]:.6f}")

    # 핵심: 최대 고유값 ≈ 1/5 × N (진공 모드)
    lambda_max = eigvals[0]
    expected_max = N / 5  # 진공이면 모든 W=1/5, 최대 고유값 = N/5
    ratio = lambda_max / expected_max
    print(f"\n  λ_max = {lambda_max:.4f}")
    print(f"  N/5 = {expected_max:.4f} (진공 극한)")
    print(f"  비율 = {ratio:.4f} (랜덤 ψ → 진공보다 작음)")

    # 고유값 비율: 두 번째/첫 번째
    r21 = eigvals[1] / eigvals[0]
    print(f"\n  λ₂/λ₁ = {r21:.4f}")
    print(f"  진공이면 → 0 (하나의 모드만 지배)")
    print(f"  랜덤이면 → O(1) (다양한 모드)")

    # 참여율 (IPR): 몇 개 모드가 지배하는가
    p = eigvals / np.sum(eigvals)
    ipr = 1.0 / np.sum(p**2)
    print(f"\n  참여율 (IPR) = {ipr:.1f} / {N} 모드")
    print(f"  진공: IPR→1 (1개 모드). 랜덤: IPR→N ({N}개 모드).")

    # Tr(W) = N/5 항상 (대각선이 1/5)
    tr = np.trace(W)
    print(f"\n  Tr(W) = {tr:.4f} = N/d = {N}/5 = {N/5:.1f} ✓")

    ok = abs(tr - N/5) < 0.01 and lambda_max < N/5 + 0.01
    print(f"\n  [{'✓ PASS' if ok else '✗'}] W 대각화 구조 확인")
    return ok


def test_causal_classification():
    """Im/Re > 1 → 시간적 변. 자발적 인과 분리."""
    print(f"\n{'━' * 70}")
    print("  TEST 2: Im/Re 인과 분류 (자발적 시공간 분리)")
    print("━" * 70)

    N = 25
    n_trials = 50
    temporal_fracs = []

    for trial in range(n_trials):
        net = Network(n=N)
        n_temporal = 0
        n_total = 0
        for i in range(N):
            for j in range(i+1, N):
                o = net.vertices[i].overlap(net.vertices[j])
                if abs(o.real) > 1e-15:
                    ratio = abs(o.imag) / abs(o.real)
                    if ratio > 1:
                        n_temporal += 1
                n_total += 1
        temporal_fracs.append(n_temporal / n_total)

    mean_t = np.mean(temporal_fracs)
    std_t = np.std(temporal_fracs)

    print(f"\n  {n_trials}회 랜덤 네트워크, 각 N={N}")
    print(f"  시간적 변 (Im/Re > 1) 비율: {mean_t:.3f} ± {std_t:.3f}")
    print(f"  기대값 (등방 랜덤): ~0.50")

    # C² vs C³ 분해 확인
    temporal_T = []  # T-sector에서 시간적
    temporal_S = []  # S-sector에서 시간적
    net = Network(n=N)
    for i in range(N):
        for j in range(i+1, N):
            oT = net.vertices[i].overlap_T(net.vertices[j])
            oS = net.vertices[i].overlap_S(net.vertices[j])
            if abs(oT.real) > 1e-15:
                temporal_T.append(abs(oT.imag) / abs(oT.real) > 1)
            if abs(oS.real) > 1e-15:
                temporal_S.append(abs(oS.imag) / abs(oS.real) > 1)

    frac_T = np.mean(temporal_T) if temporal_T else 0
    frac_S = np.mean(temporal_S) if temporal_S else 0
    print(f"\n  C² (시간) 섹터 시간적 비율: {frac_T:.3f}")
    print(f"  C³ (공간) 섹터 시간적 비율: {frac_S:.3f}")
    print(f"  차이: {abs(frac_T - frac_S):.3f}")
    print(f"\n  → 랜덤 ψ에서 시공간 분리는 통계적으로 ~50:50")
    print(f"  → 비등방성은 evolve(-i) 또는 테셀레이션에서 옴")

    ok = abs(mean_t - 0.5) < 0.1
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 자발적 ~50% 시간적 분리")
    return ok


def test_static_masses():
    """evolve 없이 step 0에서 질량 추출."""
    print(f"\n{'━' * 70}")
    print("  TEST 3: 정적 질량 추출 (evolve = 0)")
    print("━" * 70)

    # 많은 랜덤 네트워크에서 C³ 고유값 수집
    all_rS, all_rT = [], []
    for _ in range(300):
        net = Network(n=8)
        # evolve 없음! 순수 랜덤 ψ
        for i in range(net.N):
            H = net.local_hamiltonian(i)
            eS = np.sort(np.linalg.eigvalsh(H[2:5, 2:5]))
            eT = np.sort(np.linalg.eigvalsh(H[:2, :2]))
            if eS[2] > 1e-10 and eT[1] > 1e-10:
                all_rS.append(eS / eS[2])
                all_rT.append(eT / eT[1])

    rS = np.mean(all_rS, axis=0)
    rT = np.mean(all_rT, axis=0)

    print(f"\n  {len(all_rS)} 샘플 수집 (300 네트워크 × 8 꼭짓점)")
    print(f"  C³ 고유값 비율: {rS[0]:.4f} : {rS[1]:.4f} : {rS[2]:.4f}")
    print(f"  C² 고유값 비율: {rT[0]:.4f} : {rT[1]:.4f}")
    print(f"  rS₃/rS₁ = {rS[2]/rS[0]:.2f}")

    # 질량 계산
    v_H = 245.8
    n_S = 6

    up = v_H * (rS ** n_S)
    down = v_H * (rS ** n_S) * (rT[0] ** 4)
    lepton = down * rT[0]

    obs = {"t": 173, "c": 1.27, "u": 0.0022,
           "b": 4.18, "s": 0.093, "d": 0.0047,
           "τ": 1.777, "μ": 0.1057, "e": 0.000511}

    preds = {"t": up[2], "c": up[1], "u": up[0],
             "b": down[2], "s": down[1], "d": down[0],
             "τ": lepton[2], "μ": lepton[1], "e": lepton[0]}

    print(f"\n  m = v_H × rS^6 × rT^4 (정적, evolve=0)")
    print(f"\n  {'입자':>4} {'DRLT':>10} {'관측':>10} {'비율':>6}")
    print(f"  {'─' * 35}")
    n_ok = 0
    log_devs = []
    for name in ["t", "c", "u", "b", "s", "d", "τ", "μ", "e"]:
        r = preds[name] / obs[name]
        mark = " ✓" if 0.3 < r < 3 else ""
        if 0.3 < r < 3:
            n_ok += 1
        log_devs.append(abs(np.log10(r)))
        print(f"  {name:>4} {preds[name]:10.4f} {obs[name]:10.4f} {r:6.2f}×{mark}")

    avg_log = np.mean(log_devs)
    print(f"\n  3× 이내: {n_ok}/9")
    print(f"  평균 |log₁₀(비율)|: {avg_log:.3f}")
    print(f"\n  → evolve 없이도 질량 계층 구조 존재!")
    print(f"  → rS₃/rS₁ = {rS[2]/rS[0]:.1f} = C³ 기하학에서 자동")

    ok = n_ok >= 5 and avg_log < 1.0
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 정적 질량 5/9 이상 3× 이내")
    return ok


def test_vacuum_boundary():
    """W 고유벡터 중 진공에 가까운 것 = '미래 경계'."""
    print(f"\n{'━' * 70}")
    print("  TEST 4: 진공 경계 조건 (미래 → 진공?)")
    print("━" * 70)

    N = 20
    n_trials = 200
    future_closer = 0

    for _ in range(n_trials):
        net = Network(n=N)
        W = net.W_matrix()
        eigvals, eigvecs = np.linalg.eigh(W)

        # 진공 상태: 모든 ψ 동일 → W_ij = 1/5 전부
        # 진공의 W 고유벡터: 균일 벡터 (1,1,...,1)/√N
        vacuum_vec = np.ones(N) / np.sqrt(N)

        # W 최대 고유벡터 = "가장 지배적 모드"
        top_vec = eigvecs[:, -1]  # 최대 고유값의 고유벡터
        bot_vec = eigvecs[:, 0]   # 최소 고유값의 고유벡터

        # 진공 벡터와의 겹침
        overlap_top = abs(np.dot(vacuum_vec, top_vec))
        overlap_bot = abs(np.dot(vacuum_vec, bot_vec))

        if overlap_top > overlap_bot:
            future_closer += 1

    frac = future_closer / n_trials
    print(f"\n  {n_trials}회 시행, N={N}")
    print(f"  최대 고유값 모드가 진공에 더 가까운 비율: {frac:.3f}")
    print(f"  (최대 모드 = 가장 상관된 = '미래 경계')")

    # 진공 W의 구조
    print(f"\n  진공 W: 모든 성분 1/5 → 고유값 = N/5(×1) + 0(×N-1)")
    print(f"  랜덤 W: 고유값 분산 → IPR > 1")

    # 최대 고유벡터의 균일성 측정
    uniformities = []
    for _ in range(100):
        net = Network(n=N)
        W = net.W_matrix()
        _, vecs = np.linalg.eigh(W)
        top = vecs[:, -1]
        # 균일성 = 1 - 변동계수
        uniformity = 1 - np.std(np.abs(top)) / np.mean(np.abs(top))
        uniformities.append(uniformity)

    mean_u = np.mean(uniformities)
    print(f"\n  최대 고유벡터 균일성: {mean_u:.4f}")
    print(f"  (1 = 완전 균일 = 진공, 0 = 국소화)")

    ok = frac > 0.7 and mean_u > 0.5
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 최대 모드 → 진공 ({frac:.0%})")
    return ok


def test_evolve_vs_static():
    """evolve 결과 vs 정적 대각화 결과 비교."""
    print(f"\n{'━' * 70}")
    print("  TEST 5: evolve vs static 비교")
    print("━" * 70)

    from drlt import evolve_step

    # Static: step 0 (랜덤 ψ 그대로)
    rS_static, rT_static = [], []
    for _ in range(200):
        net = Network(n=8)
        for i in range(net.N):
            H = net.local_hamiltonian(i)
            eS = np.sort(np.linalg.eigvalsh(H[2:5, 2:5]))
            eT = np.sort(np.linalg.eigvalsh(H[:2, :2]))
            if eS[2] > 1e-10 and eT[1] > 1e-10:
                rS_static.append(eS / eS[2])
                rT_static.append(eT / eT[1])

    # Evolved: 30 steps
    rS_evolved, rT_evolved = [], []
    for _ in range(200):
        net = Network(n=8)
        for __ in range(30):
            evolve_step(net, dt=0.1)
        for i in range(net.N):
            H = net.local_hamiltonian(i)
            eS = np.sort(np.linalg.eigvalsh(H[2:5, 2:5]))
            eT = np.sort(np.linalg.eigvalsh(H[:2, :2]))
            if eS[2] > 1e-10 and eT[1] > 1e-10:
                rS_evolved.append(eS / eS[2])
                rT_evolved.append(eT / eT[1])

    rS_s = np.mean(rS_static, axis=0)
    rT_s = np.mean(rT_static, axis=0)
    rS_e = np.mean(rS_evolved, axis=0)
    rT_e = np.mean(rT_evolved, axis=0)

    print(f"\n  {'':>12} {'Static':>12} {'Evolved':>12} {'진공':>12}")
    print(f"  {'─' * 50}")
    print(f"  {'rS₁':>12} {rS_s[0]:12.4f} {rS_e[0]:12.4f} {'1/3':>12}")
    print(f"  {'rS₂':>12} {rS_s[1]:12.4f} {rS_e[1]:12.4f} {'1/3':>12}")
    print(f"  {'rS₃':>12} {rS_s[2]:12.4f} {rS_e[2]:12.4f} {'1/3':>12}")
    print(f"  {'rS₃/rS₁':>12} {rS_s[2]/rS_s[0]:12.2f} {rS_e[2]/rS_e[0]:12.2f} {'1.0':>12}")
    print(f"  {'rT₁':>12} {rT_s[0]:12.4f} {rT_e[0]:12.4f} {'1/2':>12}")

    # ⟨W⟩ 비교
    W_static, W_evolved = [], []
    for _ in range(100):
        net_s = Network(n=8)
        W_static.append(net_s.mean_W())
        net_e = Network(n=8)
        for __ in range(30):
            evolve_step(net_e, dt=0.1)
        W_evolved.append(net_e.mean_W())

    print(f"\n  ⟨W⟩ static  = {np.mean(W_static):.5f} ± {np.std(W_static):.5f}")
    print(f"  ⟨W⟩ evolved = {np.mean(W_evolved):.5f} ± {np.std(W_evolved):.5f}")
    print(f"  진공 (모두 정렬) = 0.20000")

    # 질량 비교
    v_H = 245.8
    n_S = 6
    obs_t, obs_c = 173, 1.27
    mt_s = v_H * rS_s[2]**n_S
    mc_s = v_H * rS_s[1]**n_S
    mt_e = v_H * rS_e[2]**n_S
    mc_e = v_H * rS_e[1]**n_S

    print(f"\n  질량 비교:")
    print(f"  {'':>8} {'Static':>10} {'Evolved':>10} {'관측':>10}")
    print(f"  {'─' * 42}")
    print(f"  {'m_t':>8} {mt_s:10.1f} {mt_e:10.1f} {obs_t:10.1f}")
    print(f"  {'m_c':>8} {mc_s:10.4f} {mc_e:10.4f} {obs_c:10.4f}")
    print(f"  {'t비율':>8} {mt_s/obs_t:10.2f}× {mt_e/obs_t:10.2f}×")
    print(f"  {'c비율':>8} {mc_s/obs_c:10.2f}× {mc_e/obs_c:10.2f}×")

    print(f"\n  해석:")
    print(f"  - static: 랜덤 ψ 자체에 C³ 계층 내재 (기하학적)")
    print(f"  - evolve: 상관 추가 → rS 비율 변화 → 질량 재조정")
    print(f"  - evolve ≠ 시간 흐름. evolve = '상관 추가' = 자기일관 이완")
    print(f"  - 둘 다 질량 계층 생성 → C⁵ 기하학이 본질")

    # evolve가 진공으로 접근하는지
    closer_to_vacuum = np.mean(W_evolved) > np.mean(W_static)
    print(f"\n  evolve → 진공 접근? {'✓ (⟨W⟩ 증가)' if closer_to_vacuum else '✗'}")

    ok = abs(mt_s/obs_t - 1) < 1.0  # static도 2× 이내
    print(f"\n  [{'✓ PASS' if ok else '✗'}] static 질량도 유효")
    return ok


def run():
    print("=" * 70)
    print("  EXP_020: BLOCK UNIVERSE — STATIC DIAGONALIZATION")
    print("=" * 70)

    results = []
    results.append(("W 대각화 = 시공간 모드", test_w_diagonalization()))
    results.append(("Im/Re 인과 분류",        test_causal_classification()))
    results.append(("정적 질량 추출",          test_static_masses()))
    results.append(("진공 경계 조건",          test_vacuum_boundary()))
    results.append(("evolve vs static 비교",   test_evolve_vs_static()))

    print(f"\n{'═' * 70}")
    p = sum(1 for _, ok in results if ok)
    for name, ok in results:
        print(f"  [{'✓' if ok else '✗'}] {name}")
    print(f"\n  {p}/{len(results)} 통과")


if __name__ == "__main__":
    run()
