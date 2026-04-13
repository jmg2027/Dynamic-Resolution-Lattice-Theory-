"""
EXP_043c: Shell-Structured Periodic Table
==========================================

Shell = lattice hop count n from SSS nucleus.
Capacity = n_T × n² = 2n² (from propagator D(n) = 1/n²).
No variational calculus. Pure topology.

n=1: 2 slots  (H, He)
n=2: 8 slots  (Li → Ne)
n=3: 18 slots (Na → Ar, ...)
n=4: 32 slots
n=5: 50 slots
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

import numpy as np
from itertools import combinations

np.set_printoptions(precision=4, suppress=True)


# ═══════════════════════════════════════════════════════════════
#  기본 도구
# ═══════════════════════════════════════════════════════════════

def normalize(v):
    n = np.linalg.norm(v)
    return v / n if n > 1e-15 else v

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

def make_T(theta, phi, c3_leak):
    """T vertex at given C² angles with specified C³ leak."""
    psi = np.zeros(5, dtype=complex)
    c2_amp = np.sqrt(1 - c3_leak**2)
    psi[0] = c2_amp * np.cos(theta) * np.exp(1j * phi)
    psi[1] = c2_amp * np.sin(theta)
    psi[2] = c3_leak / np.sqrt(3) * np.exp(1j * 0.1)
    psi[3] = c3_leak / np.sqrt(3) * np.exp(1j * 0.3)
    psi[4] = c3_leak / np.sqrt(3) * np.exp(1j * 0.7)
    return normalize(psi)


# ═══════════════════════════════════════════════════════════════
#  Shell 구조
# ═══════════════════════════════════════════════════════════════

def shell_capacity(n):
    """Shell n의 용량 = n_T × n² = 2n²."""
    return 2 * n * n

def fill_shells(Z):
    """Z개 전자를 shell 순서대로 채움.
    Returns: list of (shell_n, count_in_shell)
    """
    remaining = Z
    shells = []
    n = 1
    while remaining > 0:
        cap = shell_capacity(n)
        filled = min(remaining, cap)
        shells.append((n, filled))
        remaining -= filled
        n += 1
    return shells

def build_atom_with_shells(Z, c3_base=0.15):
    """Shell 구조를 반영한 원자 생성.

    T vertex의 C³ leak = c3_base / n² (hop distance n에서의 coupling).
    같은 shell 내 T vertex는 C² 공간에서 균등 배치.
    """
    S = [make_S(0), make_S(1), make_S(2)]
    shells = fill_shells(Z)

    T_vecs = []
    T_shells = []  # 각 T의 shell 번호

    for (n, count) in shells:
        c3_leak = c3_base / (n * n)  # coupling ∝ 1/n²

        # shell 내 T vertex 배치 (C² 공간에서 균등)
        # 각 전자 + 슬롯 = 2개씩, count개 전자 → count개 심플렉스
        for k in range(count):
            # 전자
            golden = (1 + np.sqrt(5)) / 2
            theta_e = np.pi * (k + 0.5) / count
            phi_e = 2 * np.pi * k / golden + n * 1.0  # shell마다 위상 shift
            T_vecs.append(make_T(theta_e, phi_e, c3_leak))
            T_shells.append(n)

            # 슬롯 (전자와 직교 방향)
            theta_s = np.pi - theta_e
            phi_s = phi_e + np.pi / count
            T_vecs.append(make_T(theta_s, phi_s, c3_leak))
            T_shells.append(n)

    return S, T_vecs, T_shells, shells


# ═══════════════════════════════════════════════════════════════
#  분석
# ═══════════════════════════════════════════════════════════════

def analyze_atom(Z, c3_base=0.15):
    S, T_vecs, T_shells, shells = build_atom_with_shells(Z, c3_base)

    n_electrons = Z
    n_T = len(T_vecs)  # = 2Z (electron + slot each)

    # SSS det (항상 1)
    sss_det = hinge_det(S[0], S[1], S[2])

    # SST det: S_i, S_j, T_k
    sst_by_shell = {}
    for k in range(n_T):
        n_shell = T_shells[k]
        if n_shell not in sst_by_shell:
            sst_by_shell[n_shell] = []
        for i, j in combinations(range(3), 2):
            d = hinge_det(S[i], S[j], T_vecs[k])
            sst_by_shell[n_shell].append(d)

    # STT det: S_i, T_{2k}, T_{2k+1} (같은 심플렉스 내 pair)
    stt_by_shell = {}
    for e in range(Z):
        t1_idx = 2 * e
        t2_idx = 2 * e + 1
        n_shell = T_shells[t1_idx]
        if n_shell not in stt_by_shell:
            stt_by_shell[n_shell] = []
        for i in range(3):
            d = hinge_det(S[i], T_vecs[t1_idx], T_vecs[t2_idx])
            stt_by_shell[n_shell].append(d)

    # 전체 평균
    all_sst = []
    for v in sst_by_shell.values():
        all_sst.extend(v)
    all_stt = []
    for v in stt_by_shell.values():
        all_stt.extend(v)

    return {
        'Z': Z,
        'shells': shells,
        'sss_det': sss_det,
        'sst_mean': np.mean(all_sst),
        'stt_mean': np.mean(all_stt),
        'sst_by_shell': {n: np.mean(v) for n, v in sst_by_shell.items()},
        'stt_by_shell': {n: np.mean(v) for n, v in stt_by_shell.items()},
        'sum_det': sss_det + sum(all_sst) + sum(all_stt),
    }


# ═══════════════════════════════════════════════════════════════
#  실행
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("=" * 75)
    print("EXP_043c: Shell-Structured Periodic Table")
    print("Shell capacity = 2n², coupling = c3_base/n²")
    print("=" * 75)

    elements = {
        1:'H', 2:'He', 3:'Li', 4:'Be', 5:'B', 6:'C', 7:'N', 8:'O',
        9:'F', 10:'Ne', 11:'Na', 12:'Mg', 13:'Al', 14:'Si', 15:'P',
        16:'S', 17:'Cl', 18:'Ar', 19:'K', 20:'Ca', 21:'Sc', 22:'Ti',
        23:'V', 24:'Cr', 25:'Mn', 26:'Fe', 27:'Co', 28:'Ni', 29:'Cu',
        30:'Zn', 31:'Ga', 32:'Ge', 33:'As', 34:'Se', 35:'Br', 36:'Kr',
        47:'Ag', 54:'Xe', 79:'Au', 86:'Rn', 92:'U', 118:'Og',
    }

    # 전 원소 계산
    results = []
    for Z in range(1, 119):
        results.append(analyze_atom(Z))

    # 주요 원소 출력
    print(f"\n{'Z':>4s} {'Sym':>4s} {'Shells':>20s} {'⟨SST⟩':>8s} {'⟨STT⟩':>8s}", end="")
    print(f"  STT by shell")
    print("─" * 90)

    for Z in list(range(1, 37)) + [47, 54, 79, 86, 92, 118]:
        r = results[Z - 1]
        sym = elements.get(Z, '')
        shell_str = str([(n, c) for n, c in r['shells']])
        stt_shell = ", ".join([f"n{n}:{v:.4f}" for n, v in sorted(r['stt_by_shell'].items())])
        print(f"{Z:>4d} {sym:>4s} {shell_str:>20s} {r['sst_mean']:>8.4f} {r['stt_mean']:>8.4f}  {stt_shell}")

    # ═══════════════════════════════════════════════════════════
    #  주기성 분석
    # ═══════════════════════════════════════════════════════════

    print(f"\n{'═' * 75}")
    print("주기성 분석: ⟨STT det⟩ at noble gases vs neighbors")
    print(f"{'═' * 75}")

    noble_Z = [2, 10, 18, 36, 54, 86]
    for nz in noble_Z:
        before = results[nz - 2] if nz > 1 else None
        noble = results[nz - 1]
        after = results[nz] if nz < 118 else None

        sym = elements.get(nz, f'Z={nz}')
        print(f"\n  {sym} (Z={nz}):")
        if before:
            sym_b = elements.get(nz-1, f'Z={nz-1}')
            print(f"    {sym_b:>4s} (Z={nz-1}): ⟨STT⟩ = {before['stt_mean']:.6f}")
        print(f"    {sym:>4s} (Z={nz}):  ⟨STT⟩ = {noble['stt_mean']:.6f}  ← noble gas")
        if after:
            sym_a = elements.get(nz+1, f'Z={nz+1}')
            print(f"    {sym_a:>4s} (Z={nz+1}): ⟨STT⟩ = {after['stt_mean']:.6f}")

        # Peak check
        is_peak = True
        if before and before['stt_mean'] >= noble['stt_mean']:
            is_peak = False
        if after and after['stt_mean'] >= noble['stt_mean']:
            is_peak = False
        print(f"    Local peak? {'YES ✓' if is_peak else 'NO'}")

    # STT det per shell 패턴
    print(f"\n{'═' * 75}")
    print("Shell별 STT det (1/n² 스케일링 확인)")
    print(f"{'═' * 75}")

    # He, Ne, Ar에서 각 shell의 STT det 비교
    for nz in [2, 10, 18, 36]:
        r = results[nz - 1]
        sym = elements.get(nz, '')
        print(f"\n  {sym} (Z={nz}): shells = {r['shells']}")
        for n_shell, stt_val in sorted(r['stt_by_shell'].items()):
            # 이론: STT ∝ (c3_leak)² ∝ 1/n⁴
            predicted_ratio = 1.0 / (n_shell ** 4) if n_shell > 1 else 1.0
            shell1_stt = r['stt_by_shell'].get(1, stt_val)
            actual_ratio = stt_val / shell1_stt if shell1_stt > 0 else 0
            print(f"    n={n_shell}: ⟨STT⟩ = {stt_val:.6f}, "
                  f"ratio to n=1: {actual_ratio:.4f} "
                  f"(1/n⁴ = {predicted_ratio:.4f})")

    # 결과 저장
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043c_Shell_Periodic_Table.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_043c: Shell-Structured Periodic Table\n")
        f.write("Shell = hop count n, capacity = 2n², coupling ∝ 1/n²\n")
        f.write("=" * 60 + "\n\n")
        f.write(f"{'Z':>4s} {'Sym':>4s} {'⟨STT⟩':>8s} {'Shells':>25s}\n")
        f.write("─" * 50 + "\n")
        for Z in range(1, 119):
            r = results[Z-1]
            sym = elements.get(Z, '')
            shell_str = str([(n,c) for n,c in r['shells']])
            f.write(f"{Z:>4d} {sym:>4s} {r['stt_mean']:>8.4f} {shell_str}\n")
    print(f"\n결과 저장: {outfile}")
