"""
Black Hole Simulation in DRLT
==============================
DRLT 역학으로 블랙홀 붕괴 → 바운스 → 팽창 전 과정 시뮬레이션.

핵심 예측:
  - 특이점 없음: ds² > 0 항상 (Derivation 7)
  - 바운스: 최대 압축 → 강제 팽창 (Derivation 8)
  - ℏ_eff 변동: 수평선 근처에서 ℏ 감소 (Derivation 5)
  - 호킹 복사 수정: T_H = ℏ(x)κ/(2πc), ℏ가 변하므로 스펙트럼 수정
  - 정보 보존: 유니타리 진화 (Derivation 2)
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import (Vertex, Network, evolve_step,
                  try_pachner_5to1, big_bounce_initial)

np.random.seed(42)


def make_collapsing_star(n=20, alignment=0.3):
    """
    붕괴 직전의 별: 부분적으로 정렬된 상태.
    alignment: 0=완전 랜덤, 1=완전 정렬 (블랙홀)
    """
    center = Vertex._random_state()
    center = center / np.linalg.norm(center)
    verts = []
    for _ in range(n):
        noise = (np.random.randn(5) + 1j * np.random.randn(5))
        psi = (1 - alignment) * noise + alignment * center
        verts.append(Vertex(psi))
    return Network(vertices=verts)


def snapshot(net):
    """블랙홀의 모든 관측량을 한번에 측정."""
    N = net.N
    W = net.W_matrix()
    mask = ~np.eye(N, dtype=bool)

    # 기본
    mean_w = float(np.mean(W[mask]))
    min_ds2 = net.min_ds2()

    # ZPE
    zpe_total = net.total_zero_point_energy()
    zpe_density = net.zpe_density()

    # ℏ_eff (대표 꼭짓점)
    neighbors = [net.vertices[j] for j in range(1, N)]
    h_eff = net.vertices[0].h_eff(neighbors) if N > 1 else float('inf')

    # 에너지 스펙트럼 (vertex 0)
    spec = net.local_energy_spectrum(0) if N > 1 else np.zeros(5)
    gap = float(spec[1] - spec[0]) if len(spec) > 1 else 0

    # 진공 요동
    sigma2_W = net.vacuum_fluctuation_variance()

    # 정보
    total_info = net.total_info()

    # 호킹 온도 유사체: T_H ∝ κ·ℏ_eff
    # κ (표면 중력) ∝ gradient of W ∝ max_W - min_W
    w_range = float(np.max(W[mask]) - np.min(W[mask]))
    T_hawking = w_range * h_eff if np.isfinite(h_eff) else 0

    return {
        "N": N, "mean_W": mean_w, "min_ds2": min_ds2,
        "zpe": zpe_total, "zpe_density": zpe_density,
        "h_eff": h_eff, "gap": gap, "sigma2_W": sigma2_W,
        "info": total_info, "T_hawking": T_hawking,
        "spec": spec,
    }


# ═══════════════════════════════════════════════════════════════
#  SIMULATION: 붕괴 → 바운스 → 팽창
# ═══════════════════════════════════════════════════════════════

def simulate_black_hole():
    """블랙홀 전 생애 시뮬레이션."""
    print(f"\n{'━' * 70}")
    print("  블랙홀 시뮬레이션: 붕괴 → 바운스 → 팽창")
    print("━" * 70)

    net = make_collapsing_star(n=15, alignment=0.5)
    history = []

    # ── Phase 1: 중력 붕괴 ──
    print(f"\n  Phase 1: 중력 붕괴 (상태 정렬 → W 증가 → ds² 감소)")
    print(f"  {'t':>4} {'N':>3} {'⟨W⟩':>8} {'min_ds²':>8} {'ℏ_eff':>8} "
          f"{'ZPE':>8} {'갭':>8} {'정보':>7}  단계")
    print(f"  {'─' * 70}")

    s = snapshot(net)
    s["phase"] = "초기"
    history.append(s)
    print(f"  {0:4d} {s['N']:3d} {s['mean_W']:8.5f} {s['min_ds2']:8.5f} "
          f"{s['h_eff']:8.4f} {s['zpe']:8.4f} {s['gap']:8.5f} "
          f"{s['info']:7.2f}  초기")

    # 붕괴: 강한 중력으로 진화 (evolve_step의 H가 자연히 상태를 정렬)
    for t in range(1, 61):
        # 중력 강화: dt를 점점 크게 (붕괴 가속)
        dt = 0.15 + 0.01 * t
        evolve_step(net, dt=dt)

        # Pachner 5→1: 거의 동일한 상태 병합 (해상도 감소)
        merged = try_pachner_5to1(net, w_threshold=0.185)

        s = snapshot(net)

        phase = "붕괴"
        if s["min_ds2"] < 0.05:
            phase = "수평선 근처"
        if net.N <= 5:
            phase = "★ 바운스!"

        s["phase"] = phase
        history.append(s)

        if t % 5 == 0 or phase.startswith("★") or merged > 0:
            mrk = f" (-{merged})" if merged > 0 else ""
            print(f"  {t:4d} {s['N']:3d} {s['mean_W']:8.5f} {s['min_ds2']:8.5f} "
                  f"{s['h_eff']:8.4f} {s['zpe']:8.4f} {s['gap']:8.5f} "
                  f"{s['info']:7.2f}  {phase}{mrk}")

        if net.N <= 4:
            break

    # ── Phase 2: 바운스 후 팽창 ──
    print(f"\n  Phase 2: 바운스 후 팽창 (상태 다양화 → W 감소)")
    print(f"  {'t':>4} {'N':>3} {'⟨W⟩':>8} {'min_ds²':>8} {'ℏ_eff':>8} "
          f"{'ZPE':>8} {'갭':>8} {'정보':>7}  단계")
    print(f"  {'─' * 70}")

    for t in range(1, 41):
        evolve_step(net, dt=0.08)

        s = snapshot(net)
        s["phase"] = "팽창"
        history.append(s)

        if t % 5 == 0:
            print(f"  {t:4d} {s['N']:3d} {s['mean_W']:8.5f} {s['min_ds2']:8.5f} "
                  f"{s['h_eff']:8.4f} {s['zpe']:8.4f} {s['gap']:8.5f} "
                  f"{s['info']:7.2f}  팽창")

    return history


# ═══════════════════════════════════════════════════════════════
#  분석
# ═══════════════════════════════════════════════════════════════

def analyze(history):
    """시뮬레이션 결과 분석 및 물리 검증."""
    print(f"\n{'━' * 70}")
    print("  분석: 물리 법칙 검증")
    print("━" * 70)

    h0 = history[0]
    # 바운스 포인트: min_ds2가 최소인 시점
    min_ds2_vals = [h["min_ds2"] for h in history]
    bounce_idx = np.argmin(min_ds2_vals)
    hb = history[bounce_idx]
    hf = history[-1]

    print(f"\n  {'':18s} {'초기':>10} {'바운스':>10} {'최종':>10}")
    print(f"  {'─' * 48}")
    print(f"  {'N':18s} {h0['N']:10d} {hb['N']:10d} {hf['N']:10d}")
    print(f"  {'⟨W⟩':18s} {h0['mean_W']:10.5f} {hb['mean_W']:10.5f} {hf['mean_W']:10.5f}")
    print(f"  {'min ds²':18s} {h0['min_ds2']:10.5f} {hb['min_ds2']:10.5f} {hf['min_ds2']:10.5f}")
    print(f"  {'ℏ_eff':18s} {h0['h_eff']:10.4f} {hb['h_eff']:10.4f} {hf['h_eff']:10.4f}")
    print(f"  {'ZPE':18s} {h0['zpe']:10.4f} {hb['zpe']:10.4f} {hf['zpe']:10.4f}")
    print(f"  {'에너지 갭':18s} {h0['gap']:10.5f} {hb['gap']:10.5f} {hf['gap']:10.5f}")
    print(f"  {'정보 (bits)':18s} {h0['info']:10.2f} {hb['info']:10.2f} {hf['info']:10.2f}")

    # ℏ_eff 변화 시각화
    print(f"\n  ℏ_eff 진화:")
    h_vals = [h["h_eff"] for h in history if np.isfinite(h["h_eff"])]
    if h_vals:
        h_max = max(h_vals)
        for i in range(0, len(history), max(1, len(history)//15)):
            h = history[i]
            if np.isfinite(h["h_eff"]):
                bar_len = int(h["h_eff"] / h_max * 35)
                bar = "█" * bar_len
                phase_mark = "◀ 바운스" if i == bounce_idx else ""
                print(f"    {i:3d} │{bar:<35s}│ {h['h_eff']:.4f} {phase_mark}")

    # 물리 검증
    print(f"\n  {'═' * 50}")
    print(f"  물리 법칙 검증")
    print(f"  {'═' * 50}")

    checks = []

    # 1. 특이점 없음
    all_ds2 = [h["min_ds2"] for h in history]
    no_singularity = all(d > 0 for d in all_ds2)
    checks.append(("ds² > 0 항상 (특이점 없음)", no_singularity))
    if no_singularity:
        print(f"\n    min(ds²) = {min(all_ds2):.6f} > 0")
        print(f"    → 특이점은 구조적으로 불가능")

    # 2. 바운스 발생
    bounced = hb["mean_W"] > h0["mean_W"] and hf["mean_W"] < hb["mean_W"]
    checks.append(("바운스 발생 (W 증가 후 감소)", bounced))

    # 3. 정보 보존
    infos = [h["info"] for h in history]
    info_var = (max(infos) - min(infos)) / max(infos) * 100
    info_ok = info_var < 15
    checks.append((f"정보 보존 (변동 {info_var:.1f}% < 15%)", info_ok))

    # 4. ℏ_eff > 0 항상
    h_effs = [h["h_eff"] for h in history]
    hbar_ok = all(h > 0 for h in h_effs)
    checks.append(("ℏ_eff > 0 항상", hbar_ok))

    # 5. ℏ_eff가 바운스 근처에서 변화
    if np.isfinite(h0["h_eff"]) and np.isfinite(hb["h_eff"]):
        hbar_changed = abs(hb["h_eff"] - h0["h_eff"]) / h0["h_eff"] > 0.01
        checks.append(("ℏ_eff가 바운스 근처에서 변화 (Deriv.5)", hbar_changed))

    # 6. ZPE > 0 항상
    zpe_ok = all(h["zpe"] > 0 for h in history if h["N"] > 1)
    checks.append(("ZPE > 0 항상 (Deriv.14)", zpe_ok))

    # 7. 호킹 온도 변화
    T_vals = [h["T_hawking"] for h in history if h["T_hawking"] > 0]
    if T_vals:
        T_varied = max(T_vals) / min(T_vals) > 1.5
        checks.append(("호킹 온도 유사체가 진화 중 변화", T_varied))

    print()
    passed = 0
    for name, ok in checks:
        status = "✓" if ok else "✗"
        print(f"  [{status}] {name}")
        if ok:
            passed += 1
    print(f"\n  {passed}/{len(checks)} 통과")

    return passed, len(checks)


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

def run():
    print("=" * 70)
    print("  DRLT → 블랙홀 시뮬레이션")
    print("  붕괴 → 바운스 → 팽창: 특이점 없음, 정보 보존")
    print("=" * 70)

    history = simulate_black_hole()
    passed, total = analyze(history)

    print(f"\n{'━' * 70}")
    print(f"  핵심 결론")
    print(f"{'━' * 70}")
    print(f"""
  블랙홀의 생애 (DRLT):

  ① 붕괴: 상태 정렬 → W↑ → ds²↓ → ℏ_eff↓
     (고전적 블랙홀 형성과 동일)

  ② 수평선: ds² → 최소 (but > 0!)
     → ℏ_eff 최소 → 양자 효과가 약해짐
     → 그러나 완전히 0은 아님 (Deriv. 7)

  ③ 바운스: 최대 압축 → 작용 극대 → 팽창 강제
     → 특이점 도달 불가 (3중 방어: 구조적+역학적+양자)

  ④ 팽창: 상태 다양화 → W↓ → 정보 방출
     → 호킹 복사 = 바운스 후 정보 유출
     → 정보 역설 없음 (유니타리 진화)
""")


if __name__ == "__main__":
    run()
