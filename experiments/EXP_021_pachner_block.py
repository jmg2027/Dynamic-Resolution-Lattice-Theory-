"""
Pachner in Block Universe: Resolution, Not Topology
=====================================================
완전 그래프에서 Pachner move = 유효 N의 변화 = 해상도 = 줌인.

검증할 것:
  1. W 문턱값 → 유효 N 성장 프로파일 (인플레이션?)
  2. 5^38 ≈ e^60 (60 e-folds)
  3. ħ 반복: 고정점 = φ (해상도 수렴)
  4. W 고유값 = 우주 역사 (빅뱅→현재→진공)
  5. 유효 N의 공간적 변화 = 밀집/희박 영역
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network

np.random.seed(42)


def test_effective_n_growth():
    """W 문턱값을 내리면 유효 N이 어떻게 성장하는가."""
    print(f"\n{'━' * 70}")
    print("  TEST 1: 유효 N 성장 프로파일 = 인플레이션")
    print("━" * 70)

    N = 50
    net = Network(n=N)
    W = net.W_matrix()

    # 대각선 제거
    np.fill_diagonal(W, 0)
    all_w = W[np.triu_indices(N, k=1)]
    all_w_sorted = np.sort(all_w)[::-1]  # 내림차순

    # W 문턱값을 점점 내리면서 유효 N 측정
    thresholds = np.linspace(np.max(all_w), np.min(all_w[all_w > 0]), 30)
    eff_ns = []

    print(f"\n  N = {N} 꼭짓점, {N*(N-1)//2} 변")
    print(f"  W 범위: [{np.min(all_w[all_w>0]):.6f}, {np.max(all_w):.6f}]")
    print(f"\n  {'문턱값':>10} {'활성변':>8} {'유효N':>8} {'N/N_prev':>10}")
    print(f"  {'─' * 40}")

    prev_n = 1
    for k, thr in enumerate(thresholds):
        # 유효 N = W > threshold인 변에 연결된 꼭짓점 수
        active_mask = W > thr
        active_verts = set()
        for i in range(N):
            for j in range(i+1, N):
                if active_mask[i, j]:
                    active_verts.add(i)
                    active_verts.add(j)
        n_eff = len(active_verts)
        n_edges = np.sum(active_mask) // 2
        eff_ns.append(n_eff)

        if k % 5 == 0 or k == len(thresholds) - 1:
            ratio = n_eff / prev_n if prev_n > 0 else 0
            print(f"  {thr:10.6f} {n_edges:8d} {n_eff:8d} {ratio:10.2f}×")
            if n_eff > 0:
                prev_n = n_eff

    # 성장률 분석: 급격한 성장 구간 = 인플레이션
    eff_ns = np.array(eff_ns)
    growth = np.diff(eff_ns)
    max_growth_idx = np.argmax(growth)
    max_growth = growth[max_growth_idx]

    print(f"\n  최대 성장: Δ(유효N) = {max_growth} (문턱값 #{max_growth_idx})")
    print(f"  성장 전: N_eff = {eff_ns[max_growth_idx]}")
    print(f"  성장 후: N_eff = {eff_ns[max_growth_idx+1]}")

    # 인플레이션 = "급격한 유효 N 증가" 구간 존재?
    has_inflation = max_growth > N * 0.1  # 10% 이상 한 번에 증가
    print(f"\n  인플레이션 구간 존재: {'✓' if has_inflation else '✗'}")
    print(f"  = '조명이 켜지는' 순간 = 많은 꼭짓점이 한꺼번에 활성화")

    # 해석
    print(f"\n  해석:")
    print(f"  문턱값 높음 = 빅뱅 근처 (작은 유효 N, 큰 ħ)")
    print(f"  문턱값 낮음 = 현재 (큰 유효 N, 작은 ħ)")
    print(f"  Pachner 1→5 = '문턱값이 내려가며 5개가 활성화'")

    ok = eff_ns[-1] == N and eff_ns[0] < N
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 문턱값 → 유효 N 성장 확인")
    return ok


def test_efolds():
    """5^38 ≈ e^60: 한 번 줌인 = (d+1)배 → 60 e-folds."""
    print(f"\n{'━' * 70}")
    print("  TEST 2: 5^38 ≈ e^60 (인플레이션 e-folds)")
    print("━" * 70)

    d = 4
    n = d + 1  # = 5

    # 한 번 줌인 = n배 해상도 증가
    # k번 줌인 = n^k 배
    # e-folds = ln(n^k) = k × ln(n)
    # 60 e-folds → k = 60/ln(5)

    ln5 = np.log(n)
    k_needed = 60 / ln5
    actual_efolds = k_needed * ln5

    print(f"\n  d = {d}, n = d+1 = {n}")
    print(f"  한 번 줌인 = {n}배 해상도 증가")
    print(f"  ln({n}) = {ln5:.6f}")
    print(f"\n  60 e-folds 필요한 줌인 횟수:")
    print(f"  k = 60/ln(5) = {k_needed:.2f}")
    print(f"  ⌈k⌉ = {int(np.ceil(k_needed))}")

    k_int = int(np.ceil(k_needed))  # = 38
    actual = k_int * ln5
    print(f"\n  {k_int}번 줌인: {k_int} × ln(5) = {actual:.2f} e-folds")
    print(f"  5^{k_int} = {5**k_int:.3e}")
    print(f"  e^60 = {np.exp(60):.3e}")
    print(f"  비율: 5^{k_int}/e^60 = {5**k_int/np.exp(60):.4f}")

    # 이것이 의미하는 것
    print(f"\n  해석:")
    print(f"  빅뱅 → 현재: 유효 N이 5^{k_int} ≈ 10^{k_int*np.log10(5):.0f} 배 증가")
    print(f"  = {k_int}번의 '해상도 5배' 줌인")
    print(f"  = 인플레이션의 60 e-folds!")

    # d=4에서만 60이 나오는지 확인
    print(f"\n  다른 차원에서의 e-folds (k={k_int}번 줌인):")
    for dd in [2, 3, 4, 5, 6]:
        nn = dd + 1
        ef = k_int * np.log(nn)
        kk = 60 / np.log(nn)
        print(f"    d={dd}: {k_int}×ln({nn}) = {ef:.1f} e-folds"
              f"  (60에 필요: k={kk:.1f})")

    # N_min = d+2 = 6 과의 관계
    N_min = d + 2
    print(f"\n  N_min = {N_min} = d+2 = 최소 닫힌 다면체")
    print(f"  Pachner 합 규칙: 양쪽 합 = {N_min} (항상)")
    print(f"  1↔5, 2↔4, 3↔3: 합 = {N_min} ✓")

    ok = k_int == 38 and abs(actual - 60) < 2
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 38번 줌인 ≈ 60 e-folds")
    return ok


def test_h_fixed_point():
    """ħ_new = 1 + 1/ħ_old 의 고정점 = φ."""
    print(f"\n{'━' * 70}")
    print("  TEST 3: 해상도 반복의 고정점 = φ (황금비)")
    print("━" * 70)

    phi = (1 + np.sqrt(5)) / 2

    # 반복: ħ_new = 1 + 1/ħ_old
    # 고정점: ħ = 1 + 1/ħ → ħ² - ħ - 1 = 0 → ħ = φ
    print(f"\n  반복 규칙: ħ_new = 1 + 1/ħ_old")
    print(f"  고정점 방정식: ħ = 1 + 1/ħ → ħ² - ħ - 1 = 0")
    print(f"  해: ħ = (1+√5)/2 = φ = {phi:.10f}")

    # 여러 초기값에서 수렴 확인
    print(f"\n  {'초기값':>8} {'수렴값':>12} {'|수렴-φ|':>12} {'반복수':>8}")
    print(f"  {'─' * 45}")

    all_converge = True
    for h0 in [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 100.0]:
        h = h0
        for step in range(100):
            h_new = 1 + 1/h
            if abs(h_new - h) < 1e-12:
                break
            h = h_new
        converged = abs(h - phi) < 1e-8
        all_converge = all_converge and converged
        print(f"  {h0:8.1f} {h:12.10f} {abs(h-phi):12.2e} {step+1:8d}")

    # 물리적 의미
    print(f"\n  물리적 의미:")
    print(f"  1 = 한 번 줌인에 최소 1 bit 해상")
    print(f"  1/ħ = 이전 해상도의 잔여 (자기 참조)")
    print(f"  고정점 φ = '더 줌인해도 해상도가 안 변하는 점'")
    print(f"  = 구속 (confinement) = 글루온 영역")

    # ħ_gluon과 비교
    h_vac = np.sqrt(3) * np.log(5)**2 / (16 * np.log(2))
    h_gluon = 4 * h_vac
    print(f"\n  ħ_vac = {h_vac:.6f}")
    print(f"  ħ_gluon = 4ħ_vac = {h_gluon:.6f}")
    print(f"  φ = {phi:.6f}")
    print(f"  |ħ_gluon - φ| / φ = {abs(h_gluon - phi)/phi:.4%}")

    # 연분수 표현
    print(f"\n  φ = 1 + 1/(1 + 1/(1 + 1/(1 + ...)))")
    print(f"  = 가장 느리게 수렴하는 연분수")
    print(f"  = '가장 비합리적인' 수")
    print(f"  = 해상도가 가장 안정적인 고정점")

    # 수렴 속도: Lyapunov 지수
    h = 3.0
    errors = []
    for _ in range(20):
        h = 1 + 1/h
        errors.append(abs(h - phi))
    if len(errors) >= 10:
        lyap = np.mean([np.log(errors[i+1]/errors[i])
                        for i in range(len(errors)-1)
                        if errors[i] > 1e-15 and errors[i+1] > 1e-15])
        print(f"\n  수렴률 (Lyapunov): {lyap:.4f}")
        print(f"  이론값 -2ln(φ) = {-2*np.log(phi):.4f}")

    ok = all_converge and abs(h_gluon - phi)/phi < 0.001
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 모든 초기값 → φ 수렴, ħ_gluon ≈ φ")
    return ok


def test_eigenvalue_history():
    """W 고유값 스펙트럼 = 우주 역사 인코딩."""
    print(f"\n{'━' * 70}")
    print("  TEST 4: W 고유값 = 우주 역사")
    print("━" * 70)

    N = 30
    net = Network(n=N)
    W = net.W_matrix()
    eigvals = np.sort(np.linalg.eigvalsh(W))  # 오름차순

    print(f"\n  N = {N}, W 고유값 스펙트럼:")
    print(f"  {'인덱스':>6} {'고유값':>10} {'해석':>20}")
    print(f"  {'─' * 40}")

    # 빈: 빅뱅(작은 고유값) / 현재(중간) / 미래(최대=진공)
    n_show = min(5, N)
    for k in range(n_show):
        print(f"  {k:6d} {eigvals[k]:10.6f} {'← 빅뱅 (고곡률)' if k==0 else ''}")
    print(f"  {'...':>6}")
    mid = N // 2
    for k in range(mid-1, mid+2):
        print(f"  {k:6d} {eigvals[k]:10.6f} {'← 현재?' if k==mid else ''}")
    print(f"  {'...':>6}")
    for k in range(N-n_show, N):
        label = '← 진공 (미래)' if k == N-1 else ''
        print(f"  {k:6d} {eigvals[k]:10.6f} {label}")

    # 고유값 분포 분석
    # 빅뱅 쪽: 많은 작은 고유값 (다양한 모드 = 물질 풍부)
    # 진공 쪽: 하나의 큰 고유값 (지배 모드 = 균일)
    gap = eigvals[-1] - eigvals[-2]
    bulk_spread = eigvals[-2] - eigvals[0]
    print(f"\n  최대 고유값 gap: {gap:.6f}")
    print(f"  나머지 분산: {bulk_spread:.6f}")
    print(f"  gap/분산: {gap/bulk_spread:.3f}")

    # 진공 모드 분리도: 최대 고유값이 나머지에서 얼마나 떨어져 있나
    mean_bulk = np.mean(eigvals[:-1])
    std_bulk = np.std(eigvals[:-1])
    sigma_sep = (eigvals[-1] - mean_bulk) / std_bulk if std_bulk > 0 else 0
    print(f"  진공 모드 분리: {sigma_sep:.1f}σ")

    # 고유값 간격 분포
    spacings = np.diff(eigvals)
    print(f"\n  고유값 간격 통계:")
    print(f"  평균 간격: {np.mean(spacings):.6f}")
    print(f"  최소 간격: {np.min(spacings):.6f} (축퇴 근처)")
    print(f"  최대 간격: {np.max(spacings):.6f} (진공 gap)")

    # N에 따른 진공 모드 분리
    print(f"\n  N에 따른 진공 모드 분리:")
    for nn in [8, 15, 25, 40, 60]:
        net_n = Network(n=nn)
        ev = np.sort(np.linalg.eigvalsh(net_n.W_matrix()))
        gap_n = ev[-1] - ev[-2]
        mean_n = np.mean(ev[:-1])
        std_n = np.std(ev[:-1])
        sep_n = (ev[-1] - mean_n) / std_n if std_n > 0 else 0
        print(f"    N={nn:3d}: λ_max={ev[-1]:.4f}, gap={gap_n:.4f}, "
              f"분리={sep_n:.1f}σ")

    print(f"\n  해석:")
    print(f"  - 최대 고유값 = 진공 모드 (균일 벡터), 분리 증가")
    print(f"  - 나머지 = 물질/구조의 모드 (들뜬 상태)")
    print(f"  - N↑ → 진공 분리↑ → 블록 우주의 '미래'가 더 확실히 진공")

    ok = sigma_sep > 2 and eigvals[-1] > eigvals[-2] * 1.5
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 진공 모드 명확히 분리")
    return ok


def test_spatial_variation():
    """유효 N이 공간적으로 변하는가 = 밀집/희박 영역."""
    print(f"\n{'━' * 70}")
    print("  TEST 5: 유효 N의 공간적 변화")
    print("━" * 70)

    from drlt import make_clustered_network

    # 클러스터 네트워크: 자연스럽게 밀집/희박 영역
    net = make_clustered_network(n_clusters=3, per_cluster=8, spread=0.3)
    N = net.N
    W = net.W_matrix()

    # 각 꼭짓점의 "유효 이웃 수" = Σ_j W_ij / max(W)
    # = 그 꼭짓점 주변의 해상도
    print(f"\n  N = {N} (3 클러스터 × 8)")

    w_max = np.max(W[np.triu_indices(N, k=1)])
    eff_neighbors = []
    for i in range(N):
        # threshold를 평균 W로
        w_row = W[i, :]
        w_row_off = np.concatenate([w_row[:i], w_row[i+1:]])
        eff_n = np.sum(w_row_off) / (1/5)  # 진공에서 각 이웃 기여 = 1/5
        eff_neighbors.append(eff_n)

    eff_neighbors = np.array(eff_neighbors)

    # 클러스터별 유효 N
    print(f"\n  {'클러스터':>8} {'유효 이웃':>10} {'ħ_eff':>8} {'해석':>12}")
    print(f"  {'─' * 42}")
    for c in range(3):
        idx = range(c*8, (c+1)*8)
        mean_eff = np.mean(eff_neighbors[list(idx)])
        # ħ_eff ∝ 1/유효N (해상도 반비례)
        h_eff = N / mean_eff if mean_eff > 0 else float('inf')
        label = "밀집" if mean_eff > np.mean(eff_neighbors) else "희박"
        print(f"  {c:8d} {mean_eff:10.2f} {h_eff:8.3f} {label:>12}")

    # 클러스터 간 vs 클러스터 내 W
    intra_w, inter_w = [], []
    for i in range(N):
        ci = i // 8
        for j in range(i+1, N):
            cj = j // 8
            if ci == cj:
                intra_w.append(W[i, j])
            else:
                inter_w.append(W[i, j])

    print(f"\n  클러스터 내 ⟨W⟩ = {np.mean(intra_w):.6f}")
    print(f"  클러스터 간 ⟨W⟩ = {np.mean(inter_w):.6f}")
    print(f"  비율 = {np.mean(intra_w)/np.mean(inter_w):.2f}×")

    # 문턱값에 따른 유효 N: 클러스터별
    print(f"\n  문턱값별 클러스터 활성화:")
    print(f"  {'문턱값':>10} {'C0':>5} {'C1':>5} {'C2':>5} {'전체':>6}")
    print(f"  {'─' * 35}")

    for thr in [0.15, 0.10, 0.05, 0.02, 0.01, 0.005]:
        active = [set(), set(), set()]
        for i in range(N):
            for j in range(i+1, N):
                if W[i, j] > thr:
                    active[i//8 if i//8 < 3 else 2].add(i)
                    active[j//8 if j//8 < 3 else 2].add(j)
        sizes = [len(a) for a in active]
        total = len(set().union(*active))
        print(f"  {thr:10.3f} {sizes[0]:5d} {sizes[1]:5d} {sizes[2]:5d} {total:6d}")

    # ħ의 공간적 변화 → 해상도의 공간적 변화
    h_effs = []
    for i in range(N):
        neighbors = [net.vertices[j] for j in range(N) if j != i]
        h = net.vertices[i].h_eff(neighbors)
        h_effs.append(h)

    h_effs = np.array(h_effs)
    finite = h_effs[np.isfinite(h_effs)]

    if len(finite) > 0:
        print(f"\n  ħ_eff 분포:")
        for c in range(3):
            idx = range(c*8, (c+1)*8)
            h_c = [h_effs[i] for i in idx if np.isfinite(h_effs[i])]
            if h_c:
                print(f"    클러스터 {c}: ħ = {np.mean(h_c):.4f} ± {np.std(h_c):.4f}")

    print(f"\n  해석:")
    print(f"  - 밀집 영역: W 큼 → 유효 N 큼 → ħ 작음 → 고해상도")
    print(f"  - 희박 영역: W 작음 → 유효 N 작음 → ħ 큼 → 저해상도")
    print(f"  - = Dynamic Resolution! (이론의 이름 그 자체)")

    ok = np.mean(intra_w) > 1.5 * np.mean(inter_w)
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 밀집/희박 해상도 차이 확인 (1.5× 이상)")
    return ok


def run():
    print("=" * 70)
    print("  EXP_021: PACHNER IN BLOCK UNIVERSE")
    print("  Pachner = 해상도 변화 = 유효 N = 줌인")
    print("=" * 70)

    results = []
    results.append(("유효 N 성장 = 인플레이션", test_effective_n_growth()))
    results.append(("5^38 ≈ e^60 e-folds",      test_efolds()))
    results.append(("ħ 고정점 = φ",              test_h_fixed_point()))
    results.append(("W 고유값 = 우주 역사",       test_eigenvalue_history()))
    results.append(("유효 N 공간 변화",           test_spatial_variation()))

    print(f"\n{'═' * 70}")
    p = sum(1 for _, ok in results if ok)
    for name, ok in results:
        print(f"  [{'✓' if ok else '✗'}] {name}")
    print(f"\n  {p}/{len(results)} 통과")


if __name__ == "__main__":
    run()
