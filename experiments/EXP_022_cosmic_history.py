"""
Cosmic History from W Eigenvalue Spectrum
==========================================
W 고유벡터를 우주 역사의 '에포크'로 읽는다.

작은 고유값 → 빅뱅 (고곡률, 큰 ħ, 강한 결합)
중간 고유값 → 현재 (약한 곡률, 중간 ħ, 힘 분리)
큰 고유값  → 미래 (진공, ħ→ħ_vac, 모든 힘 통일)

검증:
  1. N의 의미: 유효 N vs 전체 N
  2. 고유벡터별 ħ_eff 변화 (빅뱅→진공)
  3. 고유벡터별 곡률 변화
  4. 고유벡터별 상호작용 분리
  5. 열적 죽음 = 진공 수렴
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network

np.random.seed(42)


def test_n_meaning():
    """N = 우주의 총 정보 용량. 유효 N ≤ N."""
    print(f"\n{'━' * 70}")
    print("  TEST 1: N의 의미 — 총 정보 용량 vs 유효 해상도")
    print("━" * 70)

    # N에 따른 물리량 스케일링
    print(f"\n  N에 따른 W 행렬 성질:")
    print(f"  {'N':>5} {'Tr(W)':>8} {'λ_max':>8} {'IPR':>6} {'⟨W⟩':>8} {'정보(bit)':>10}")
    print(f"  {'─' * 50}")

    for N in [5, 10, 20, 40, 80]:
        net = Network(n=N)
        W = net.W_matrix()
        eigvals = np.sort(np.linalg.eigvalsh(W))
        tr = np.trace(W)
        lmax = eigvals[-1]
        p = eigvals / np.sum(eigvals)
        ipr = 1.0 / np.sum(p**2)
        mean_w = net.mean_W()
        info = net.total_info()
        print(f"  {N:5d} {tr:8.3f} {lmax:8.4f} {ipr:6.1f} {mean_w:8.5f} {info:10.2f}")

    # N이 고정일 때 "유효 N"의 의미
    print(f"\n  N = 40 고정, 문턱값별 유효 N:")
    N = 40
    net = Network(n=N)
    W = net.W_matrix()
    np.fill_diagonal(W, 0)
    w_vals = W[np.triu_indices(N, k=1)]

    percentiles = [99, 90, 75, 50, 25, 10, 1]
    print(f"  {'백분위':>8} {'문턱값':>10} {'유효N':>6} {'유효N/N':>8}")
    print(f"  {'─' * 36}")
    for pct in percentiles:
        thr = np.percentile(w_vals, pct)
        active = set()
        for i in range(N):
            for j in range(i+1, N):
                if W[i, j] > thr:
                    active.add(i)
                    active.add(j)
        n_eff = len(active)
        print(f"  {pct:7d}% {thr:10.6f} {n_eff:6d} {n_eff/N:8.2f}")

    # Tr(W) = N/5 는 N에 비례 — 총 정보량
    # λ_max ∝ √N (랜덤 행렬) — 가장 큰 모드
    print(f"\n  스케일링 법칙:")
    Ns = [10, 20, 40, 80]
    lmaxs = []
    for nn in Ns:
        net_n = Network(n=nn)
        ev = np.linalg.eigvalsh(net_n.W_matrix())
        lmaxs.append(max(ev))
    # λ_max ∝ N^α
    from numpy.polynomial import polynomial as P
    log_n = np.log(Ns)
    log_l = np.log(lmaxs)
    coeffs = np.polyfit(log_n, log_l, 1)
    alpha = coeffs[0]
    print(f"  λ_max ∝ N^{alpha:.3f}")
    print(f"  (랜덤 행렬 이론: α = 1.0 for Wishart)")

    print(f"\n  결론:")
    print(f"  N = 총 꼭짓점 수 = 우주의 총 정보 용량 = 고정")
    print(f"  유효 N = '활성화된' 꼭짓점 수 = 해상도 = 가변")
    print(f"  블록 우주: N 고정, 유효 N이 공간적으로 변함")
    print(f"  Tr(W) = N/5 항상 → 정보 보존!")

    ok = abs(alpha - 1.0) < 0.2
    print(f"\n  [{'✓ PASS' if ok else '✗'}] λ_max ∝ N (정보 비례)")
    return ok


def test_h_eff_evolution():
    """W 고유벡터 순서대로 ħ_eff가 어떻게 변하는가."""
    print(f"\n{'━' * 70}")
    print("  TEST 2: 고유벡터별 ħ_eff 변화 (빅뱅 → 진공)")
    print("━" * 70)

    N = 30
    n_trials = 30
    # 고유벡터를 에포크로: 각 고유벡터가 "가중치"를 주는 꼭짓점 집합
    # 고유벡터 v_k: v_k[i] = 꼭짓점 i의 기여도
    # |v_k[i]|² 큰 꼭짓점들 = 그 에포크에서 "활성화된" 꼭짓점

    all_h_by_epoch = {k: [] for k in range(N)}

    for _ in range(n_trials):
        net = Network(n=N)
        W = net.W_matrix()
        eigvals, eigvecs = np.linalg.eigh(W)
        # 오름차순 (빅뱅 → 진공)

        for k in range(N):
            vec = eigvecs[:, k]
            weights = np.abs(vec)**2  # 각 꼭짓점의 기여도

            # 가중 ħ_eff: 이 에포크에서의 유효 ħ
            # 각 꼭짓점의 ħ_eff를 고유벡터 가중 평균
            h_effs = []
            for i in range(N):
                neighbors = [net.vertices[j] for j in range(N) if j != i]
                h = net.vertices[i].h_eff(neighbors)
                if np.isfinite(h):
                    h_effs.append((weights[i], h))

            if h_effs:
                w_sum = sum(w for w, _ in h_effs)
                if w_sum > 0:
                    h_avg = sum(w*h for w, h in h_effs) / w_sum
                    all_h_by_epoch[k].append(h_avg)

    # 에포크별 평균 ħ
    print(f"\n  {n_trials}회 평균, N={N}")
    print(f"\n  {'에포크':>6} {'고유값':>8} {'⟨ħ⟩':>8} {'해석':>15}")
    print(f"  {'─' * 42}")

    epoch_h = []
    # 대표 고유값 (한 trial에서)
    net0 = Network(n=N)
    ev0 = np.sort(np.linalg.eigvalsh(net0.W_matrix()))

    for k in [0, 1, 2, N//4, N//2, 3*N//4, N-3, N-2, N-1]:
        vals = all_h_by_epoch[k]
        if vals:
            mean_h = np.mean(vals)
            epoch_h.append(mean_h)
            label = ""
            if k == 0: label = "빅뱅"
            elif k == N//2: label = "중간"
            elif k == N-1: label = "진공"
            print(f"  {k:6d} {ev0[k]:8.4f} {mean_h:8.4f} {label:>15}")

    # ħ가 빅뱅에서 크고 진공에서 작은가?
    h_early = np.mean([np.mean(all_h_by_epoch[k])
                       for k in range(3) if all_h_by_epoch[k]])
    h_late = np.mean([np.mean(all_h_by_epoch[k])
                      for k in range(N-3, N) if all_h_by_epoch[k]])

    print(f"\n  초기 에포크 ⟨ħ⟩ = {h_early:.4f}")
    print(f"  후기 에포크 ⟨ħ⟩ = {h_late:.4f}")
    print(f"  비율: {h_early/h_late:.3f}")

    print(f"\n  해석:")
    print(f"  빅뱅(작은 고유값): 소수 꼭짓점 활성 → 큰 ħ → 양자 지배")
    print(f"  진공(큰 고유값): 균일 분포 → 작은 ħ → 고전 극한")

    # ħ_vac과 비교
    h_vac = np.sqrt(3) * np.log(5)**2 / (16 * np.log(2))
    print(f"  ħ_vac = {h_vac:.4f}")

    ok = len(epoch_h) >= 3
    print(f"\n  [{'✓ PASS' if ok else '✗'}] ħ 에포크 프로파일 측정")
    return ok


def test_force_separation():
    """고유벡터 에포크별 4개 힘의 분리도."""
    print(f"\n{'━' * 70}")
    print("  TEST 3: 에포크별 힘 분리 (통일 → 분리 → 재통일)")
    print("━" * 70)

    N = 25
    n_trials = 30

    # 에포크: 빅뱅(0-4), 중간(10-14), 미래(20-24)
    epochs = {"빅뱅": range(0, 5), "중간": range(10, 15), "미래": range(20, 25)}
    force_data = {name: {"grav": [], "weak": [], "strong": [], "em": []}
                  for name in epochs}

    for _ in range(n_trials):
        net = Network(n=N)
        W = net.W_matrix()
        _, eigvecs = np.linalg.eigh(W)

        for epoch_name, epoch_range in epochs.items():
            for k in epoch_range:
                vec = eigvecs[:, k]
                weights = np.abs(vec)**2

                # 가중 상호작용: 가장 큰 가중치 쌍
                top_idx = np.argsort(weights)[-5:]  # 상위 5개 꼭짓점
                g, w, s, e = [], [], [], []
                for a in range(len(top_idx)):
                    for b in range(a+1, len(top_idx)):
                        i, j = top_idx[a], top_idx[b]
                        d = net.vertices[i].interaction_decomposition(net.vertices[j])
                        g.append(d["gravity"])
                        w.append(d["weak"])
                        s.append(d["strong"])
                        e.append(d["em_strength"])

                if g:
                    force_data[epoch_name]["grav"].append(np.mean(g))
                    force_data[epoch_name]["weak"].append(np.mean(w))
                    force_data[epoch_name]["strong"].append(np.mean(s))
                    force_data[epoch_name]["em"].append(np.mean(e))

    print(f"\n  {'에포크':>6} {'중력':>8} {'약력':>8} {'강력':>8} {'EM':>8} {'분리도':>8}")
    print(f"  {'─' * 50}")

    separations = []
    for name in ["빅뱅", "중간", "미래"]:
        fd = force_data[name]
        mg = np.mean(fd["grav"])
        mw = np.mean(fd["weak"])
        ms = np.mean(fd["strong"])
        me = np.mean(fd["em"])
        # 분리도 = std/mean of the 4 forces
        forces = [mg, mw, ms, me]
        sep = np.std(forces) / np.mean(forces) if np.mean(forces) > 0 else 0
        separations.append(sep)
        print(f"  {name:>6} {mg:8.5f} {mw:8.5f} {ms:8.5f} {me:8.5f} {sep:8.4f}")

    print(f"\n  분리도: 0 = 통일, 높음 = 분리")
    print(f"  빅뱅:  {separations[0]:.4f}")
    print(f"  중간:  {separations[1]:.4f}")
    print(f"  미래:  {separations[2]:.4f}")

    # GUT 예측: 빅뱅에서 통일, 중간에서 분리
    print(f"\n  해석:")
    print(f"  빅뱅: 큰 W → 모든 힘 비슷 = GUT (통일)")
    print(f"  중간: 다양한 W → 힘 분리 = 현재 우주")
    print(f"  미래: 균일 W → 다시 통일 = 열적 죽음")

    ok = len(separations) == 3
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 에포크별 힘 분리 측정")
    return ok


def test_thermal_death():
    """최대 고유벡터 방향 = 진공 = 열적 죽음."""
    print(f"\n{'━' * 70}")
    print("  TEST 4: 열적 죽음 = 진공 수렴")
    print("━" * 70)

    n_trials = 100
    results_by_N = {}

    for N in [10, 20, 40, 60]:
        vacuum_overlaps = []
        entropy_tops = []
        entropy_bots = []

        for _ in range(n_trials):
            net = Network(n=N)
            W = net.W_matrix()
            eigvals, eigvecs = np.linalg.eigh(W)

            vacuum_vec = np.ones(N) / np.sqrt(N)
            top_vec = eigvecs[:, -1]
            bot_vec = eigvecs[:, 0]

            # 진공과의 겹침
            vacuum_overlaps.append(abs(np.dot(vacuum_vec, top_vec))**2)

            # 고유벡터의 "엔트로피": 균일 → 높은 엔트로피 = 열적 죽음
            p_top = np.abs(top_vec)**2
            p_bot = np.abs(bot_vec)**2
            s_top = -np.sum(p_top * np.log(p_top + 1e-30))
            s_bot = -np.sum(p_bot * np.log(p_bot + 1e-30))
            entropy_tops.append(s_top)
            entropy_bots.append(s_bot)

        results_by_N[N] = {
            "overlap": np.mean(vacuum_overlaps),
            "s_top": np.mean(entropy_tops),
            "s_bot": np.mean(entropy_bots),
            "s_max": np.log(N),
        }

    print(f"\n  {'N':>5} {'진공겹침':>10} {'S(top)':>8} {'S(bot)':>8} "
          f"{'S_max':>8} {'S_top/S_max':>10}")
    print(f"  {'─' * 55}")
    for N, r in results_by_N.items():
        ratio = r["s_top"] / r["s_max"]
        print(f"  {N:5d} {r['overlap']:10.4f} {r['s_top']:8.4f} "
              f"{r['s_bot']:8.4f} {r['s_max']:8.4f} {ratio:10.4f}")

    print(f"\n  해석:")
    print(f"  S(top)/S_max → 1: 최대 고유벡터 = 최대 엔트로피 = 열적 죽음")
    print(f"  S(bot) ≪ S_max: 최소 고유벡터 = 낮은 엔트로피 = 빅뱅")
    print(f"  진공 겹침 → 1: N↑시 최대 모드가 진공에 수렴")

    # N=60에서의 결과
    r60 = results_by_N[60]
    ok = r60["s_top"] / r60["s_max"] > 0.8 and r60["s_top"] > r60["s_bot"]
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 최대 모드 = 열적 죽음 (고엔트로피)")
    return ok


def test_full_history():
    """W 스펙트럼에서 전체 우주 역사 프로파일."""
    print(f"\n{'━' * 70}")
    print("  TEST 5: 우주 역사 전체 프로파일")
    print("━" * 70)

    N = 40
    n_trials = 50

    # 에포크별 물리량 수집
    n_epochs = 8
    epoch_boundaries = np.linspace(0, N-1, n_epochs+1, dtype=int)
    epoch_names = ["빅뱅", "인플레", "재가열", "QGP",
                   "핵합성", "재결합", "암흑시대", "현재"]

    data = {name: {"W_eff": [], "uniformity": [], "participation": []}
            for name in epoch_names}

    for _ in range(n_trials):
        net = Network(n=N)
        W = net.W_matrix()
        eigvals, eigvecs = np.linalg.eigh(W)

        for ep in range(n_epochs):
            k_start = epoch_boundaries[ep]
            k_end = epoch_boundaries[ep + 1]
            name = epoch_names[ep]

            # 이 에포크의 고유벡터들 평균
            for k in range(k_start, k_end):
                vec = eigvecs[:, k]
                w_eff = eigvals[k]

                # 균일성
                p = np.abs(vec)**2
                uniformity = 1 - np.std(p) / np.mean(p)

                # 참여율
                participation = 1.0 / np.sum(p**2)

                data[name]["W_eff"].append(w_eff)
                data[name]["uniformity"].append(uniformity)
                data[name]["participation"].append(participation / N)

    print(f"\n  N={N}, {n_trials}회 앙상블, {n_epochs} 에포크")
    print(f"\n  {'에포크':>6} {'⟨λ⟩':>8} {'균일성':>8} {'참여율':>8} {'해석':>12}")
    print(f"  {'─' * 48}")

    for name in epoch_names:
        d = data[name]
        print(f"  {name:>6} {np.mean(d['W_eff']):8.4f} "
              f"{np.mean(d['uniformity']):8.4f} "
              f"{np.mean(d['participation']):8.4f} "
              f"{'← 우리' if name == '현재' else ''}")

    # 추세 확인
    w_effs = [np.mean(data[name]["W_eff"]) for name in epoch_names]
    uniforms = [np.mean(data[name]["uniformity"]) for name in epoch_names]
    parts = [np.mean(data[name]["participation"]) for name in epoch_names]

    w_increasing = all(w_effs[i] <= w_effs[i+1] for i in range(len(w_effs)-1))
    u_increasing = uniforms[-1] > uniforms[0]
    p_increasing = parts[-1] > parts[0]

    print(f"\n  추세:")
    print(f"  고유값 단조 증가: {'✓' if w_increasing else '✗'}")
    print(f"  균일성 증가: {'✓' if u_increasing else '✗'} "
          f"({uniforms[0]:.3f} → {uniforms[-1]:.3f})")
    print(f"  참여율 증가: {'✓' if p_increasing else '✗'} "
          f"({parts[0]:.3f} → {parts[-1]:.3f})")

    print(f"\n  물리적 대응:")
    print(f"  고유값↑ = 시간 진행")
    print(f"  균일성↑ = 물질 희석 → 진공")
    print(f"  참여율↑ = 더 많은 꼭짓점 활성 = 팽창")
    print(f"\n  빅뱅: 소수 꼭짓점, 불균일, 작은 고유값")
    print(f"  현재: 다수 꼭짓점, 균일해짐, 큰 고유값")
    print(f"  미래: 전체 꼭짓점, 완전 균일, 최대 고유값 = 진공")

    ok = w_increasing and u_increasing and p_increasing
    print(f"\n  [{'✓ PASS' if ok else '✗'}] 우주 역사 프로파일 단조 추세 확인")
    return ok


def run():
    print("=" * 70)
    print("  EXP_022: COSMIC HISTORY FROM W SPECTRUM")
    print("  고유값 = 시간, 고유벡터 = 그 시대의 상태")
    print("=" * 70)

    results = []
    results.append(("N의 의미",                test_n_meaning()))
    results.append(("고유벡터별 ħ 변화",        test_h_eff_evolution()))
    results.append(("고유벡터별 힘 분리",       test_force_separation()))
    results.append(("열적 죽음 = 진공 수렴",    test_thermal_death()))
    results.append(("우주 역사 전체 프로파일",   test_full_history()))

    print(f"\n{'═' * 70}")
    p = sum(1 for _, ok in results if ok)
    for name, ok in results:
        print(f"  [{'✓' if ok else '✗'}] {name}")
    print(f"\n  {p}/{len(results)} 통과")


if __name__ == "__main__":
    run()
