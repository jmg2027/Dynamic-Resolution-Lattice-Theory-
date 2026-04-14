"""
EXP_043b: Simplex Anatomy — All Elements (Z=1 to 118)
======================================================

원자번호 Z = 심플렉스 개수 (SSS 핵 공유).
각 원소에서: 힌지 수, det 분포, STT det 변화, T-T 중첩 패턴.

핵심 질문: Z가 커지면 C² 공간에서 T 벡터가 "빽빽해지는" 효과가
det 값에 어떻게 나타나는가?
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

import numpy as np
from itertools import combinations

np.set_printoptions(precision=4, suppress=True)


def normalize(v):
    return v / np.linalg.norm(v)

def hinge_det(v1, v2, v3):
    G = np.array([
        [np.vdot(v1,v1), np.vdot(v1,v2), np.vdot(v1,v3)],
        [np.vdot(v2,v1), np.vdot(v2,v2), np.vdot(v2,v3)],
        [np.vdot(v3,v1), np.vdot(v3,v2), np.vdot(v3,v3)],
    ])
    return float(np.real(np.linalg.det(G)))

def make_S(direction):
    psi = np.zeros(5, dtype=complex)
    psi[2 + direction] = 1.0
    return psi

def make_T(theta, phi, c3_leak=0.05):
    psi = np.zeros(5, dtype=complex)
    c2_amp = np.sqrt(1 - c3_leak**2)
    psi[0] = c2_amp * np.cos(theta) * np.exp(1j * phi)
    psi[1] = c2_amp * np.sin(theta)
    psi[2] = c3_leak / np.sqrt(3) * np.exp(1j * 0.1)
    psi[3] = c3_leak / np.sqrt(3) * np.exp(1j * 0.3)
    psi[4] = c3_leak / np.sqrt(3) * np.exp(1j * 0.7)
    return normalize(psi)


def analyze_element(Z):
    """원자번호 Z에 대해 심플렉스 구조 분석."""
    # SSS 핵 (항상 동일)
    S = [make_S(0), make_S(1), make_S(2)]

    # T 꼭짓점들: C² 공간에 균등 분포
    # 2Z개 (전자 Z + 슬롯 Z)
    T_vecs = []
    for k in range(2 * Z):
        # C² 공간에서 균등 분포 (golden angle로)
        golden = (1 + np.sqrt(5)) / 2
        theta = np.arccos(1 - 2 * (k + 0.5) / (2 * Z))  # [0, π]
        phi = 2 * np.pi * k / golden  # golden angle
        T_vecs.append(make_T(theta, phi, c3_leak=0.05))

    # 심플렉스: Z개, 각각 S₁S₂S₃ + T_{2k}, T_{2k+1}
    # 힌지 분석
    sss_dets = []
    sst_dets = []
    stt_dets = []

    # SSS (1개, 공유)
    sss_dets.append(hinge_det(S[0], S[1], S[2]))

    for k in range(Z):
        T1 = T_vecs[2*k]
        T2 = T_vecs[2*k + 1]

        # SST 힌지 (6개 per simplex)
        for i, j in combinations(range(3), 2):
            sst_dets.append(hinge_det(S[i], S[j], T1))
            sst_dets.append(hinge_det(S[i], S[j], T2))

        # STT 힌지 (3개 per simplex)
        for i in range(3):
            stt_dets.append(hinge_det(S[i], T1, T2))

    # T-T 중첩 (모든 T 쌍)
    n_T = len(T_vecs)
    tt_overlaps = []
    for i in range(n_T):
        for j in range(i+1, n_T):
            tt_overlaps.append(abs(np.vdot(T_vecs[i], T_vecs[j])))

    # 힌지 수
    n_hinges = 1 + 6*Z + 3*Z  # = 1 + 9Z

    return {
        'Z': Z,
        'n_simplices': Z,
        'n_hinges': n_hinges,
        'n_vertices': 3 + 2*Z,
        'sss_det': np.mean(sss_dets),
        'sst_det_mean': np.mean(sst_dets),
        'sst_det_std': np.std(sst_dets),
        'stt_det_mean': np.mean(stt_dets),
        'stt_det_std': np.std(stt_dets),
        'stt_det_min': np.min(stt_dets),
        'stt_det_max': np.max(stt_dets),
        'sum_det': sum(sss_dets) + sum(sst_dets) + sum(stt_dets),
        'tt_overlap_mean': np.mean(tt_overlaps) if tt_overlaps else 0,
        'tt_overlap_max': np.max(tt_overlaps) if tt_overlaps else 0,
    }


# ═══════════════════════════════════════════════════════════════
#  전 원소 계산
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("=" * 80)
    print("EXP_043b: Simplex Anatomy — All Elements Z=1 to 118")
    print("=" * 80)

    elements = {
        1: 'H', 2: 'He', 3: 'Li', 4: 'Be', 5: 'B', 6: 'C', 7: 'N', 8: 'O',
        9: 'F', 10: 'Ne', 11: 'Na', 12: 'Mg', 13: 'Al', 14: 'Si', 15: 'P',
        16: 'S', 17: 'Cl', 18: 'Ar', 19: 'K', 20: 'Ca', 26: 'Fe', 29: 'Cu',
        47: 'Ag', 79: 'Au', 82: 'Pb', 92: 'U', 118: 'Og',
    }

    results = []
    all_Z = list(range(1, 119))

    print(f"\n{'Z':>4s} {'Sym':>4s} {'Simp':>5s} {'Hing':>5s} {'SSS':>8s} "
          f"{'⟨SST⟩':>8s} {'⟨STT⟩':>8s} {'STT min':>8s} {'STT max':>8s} "
          f"{'⟨TT⟩':>7s} {'TT max':>7s} {'Σdet':>10s}")
    print("─" * 95)

    for Z in all_Z:
        r = analyze_element(Z)
        results.append(r)
        sym = elements.get(Z, '')
        if Z <= 20 or Z in elements:
            print(f"{Z:>4d} {sym:>4s} {r['n_simplices']:>5d} {r['n_hinges']:>5d} "
                  f"{r['sss_det']:>8.4f} {r['sst_det_mean']:>8.4f} "
                  f"{r['stt_det_mean']:>8.4f} {r['stt_det_min']:>8.4f} "
                  f"{r['stt_det_max']:>8.4f} {r['tt_overlap_mean']:>7.4f} "
                  f"{r['tt_overlap_max']:>7.4f} {r['sum_det']:>10.2f}")

    # ═══════════════════════════════════════════════════════════
    #  패턴 분석
    # ═══════════════════════════════════════════════════════════

    print(f"\n{'═' * 80}")
    print("패턴 분석")
    print(f"{'═' * 80}")

    Zs = [r['Z'] for r in results]
    sum_dets = [r['sum_det'] for r in results]
    stt_means = [r['stt_det_mean'] for r in results]
    tt_means = [r['tt_overlap_mean'] for r in results]
    tt_maxs = [r['tt_overlap_max'] for r in results]

    # Σdet vs Z 스케일링
    # Σdet = 1 + 6Z × ⟨SST⟩ + 3Z × ⟨STT⟩ ≈ 1 + 6Z(0.998) + 3Z⟨STT⟩
    print(f"\n1) Σdet 스케일링:")
    print(f"   Σdet(H) = {results[0]['sum_det']:.4f}")
    print(f"   Σdet(Z) ≈ 1 + 5.990Z + 3Z⟨STT(Z)⟩")
    for Z_check in [1, 2, 10, 20, 50, 118]:
        r = results[Z_check - 1]
        predicted = 1 + 5.990 * Z_check + 3 * Z_check * r['stt_det_mean']
        print(f"   Z={Z_check:3d}: Σdet = {r['sum_det']:10.2f}, "
              f"predicted = {predicted:10.2f}, "
              f"ratio = {r['sum_det']/predicted:.4f}")

    # STT det vs Z (핵심!)
    print(f"\n2) ⟨STT det⟩ vs Z (약력/화학의 변화):")
    for Z_check in [1, 2, 5, 10, 18, 36, 54, 86, 118]:
        if Z_check <= 118:
            r = results[Z_check - 1]
            print(f"   Z={Z_check:3d}: ⟨STT⟩ = {r['stt_det_mean']:.6f}, "
                  f"range [{r['stt_det_min']:.4f}, {r['stt_det_max']:.4f}], "
                  f"σ = {r['stt_det_std']:.4f}")

    # T-T 중첩 vs Z (C² 공간 포화)
    print(f"\n3) T-T 중첩 vs Z (C² 공간 포화도):")
    for Z_check in [1, 2, 5, 10, 20, 50, 118]:
        r = results[Z_check - 1]
        print(f"   Z={Z_check:3d}: ⟨|⟨T_i|T_j⟩|⟩ = {r['tt_overlap_mean']:.4f}, "
              f"max = {r['tt_overlap_max']:.4f}")

    # 주기율표 구조 확인
    print(f"\n4) 비활성 기체에서의 STT det (껍질 닫힘):")
    noble = [2, 10, 18, 36, 54, 86, 118]
    for Z in noble:
        r = results[Z - 1]
        sym = elements.get(Z, f'Z={Z}')
        print(f"   {sym:>4s} (Z={Z:3d}): ⟨STT⟩ = {r['stt_det_mean']:.6f}, "
              f"TT_max = {r['tt_overlap_max']:.4f}")

    # 결과 저장
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043b_All_Elements.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_043b: Simplex Anatomy — All Elements Z=1 to 118\n")
        f.write("=" * 70 + "\n\n")
        f.write(f"{'Z':>4s} {'Simp':>5s} {'Hing':>5s} {'⟨SST⟩':>8s} {'⟨STT⟩':>8s} "
                f"{'STT_min':>8s} {'STT_max':>8s} {'⟨TT⟩':>7s} {'Σdet':>10s}\n")
        f.write("─" * 70 + "\n")
        for r in results:
            f.write(f"{r['Z']:>4d} {r['n_simplices']:>5d} {r['n_hinges']:>5d} "
                    f"{r['sst_det_mean']:>8.4f} {r['stt_det_mean']:>8.4f} "
                    f"{r['stt_det_min']:>8.4f} {r['stt_det_max']:>8.4f} "
                    f"{r['tt_overlap_mean']:>7.4f} {r['sum_det']:>10.2f}\n")
    print(f"\n결과 저장: {outfile}")
