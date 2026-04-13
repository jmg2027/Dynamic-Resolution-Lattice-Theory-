"""
EXP_043: Simplex Anatomy — Numerical Geometry of Atoms
=======================================================

그림(book/figures/)의 심플렉스 구조를 숫자로 계산.
각 원자에 대해:
  1. ψ 벡터 배치 (S는 C³ 직교, T는 C² + 작은 C³ leak)
  2. Gram 행렬 G_ij = ⟨ψ_i|ψ_j⟩
  3. 모든 힌지의 det(G_h), 면적 A_h, 분류 (SSS/SST/STT)
  4. Regge action S = Σ A_h δ_h
  5. 물리량: ħ_eff, 힘 비율, 결합 에너지 비
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

import numpy as np
from itertools import combinations

np.set_printoptions(precision=6, suppress=True)

print("=" * 65)
print("EXP_043: Simplex Anatomy — Numerical Geometry of Atoms")
print("=" * 65)


# ═══════════════════════════════════════════════════════════════
#  기본 도구
# ═══════════════════════════════════════════════════════════════

def normalize(v):
    return v / np.linalg.norm(v)

def gram(vecs):
    """N×N Gram matrix."""
    n = len(vecs)
    G = np.zeros((n, n), dtype=complex)
    for i in range(n):
        for j in range(n):
            G[i, j] = np.vdot(vecs[i], vecs[j])
    return G

def hinge_det(v1, v2, v3):
    G = gram([v1, v2, v3])
    return float(np.real(np.linalg.det(G)))

def hinge_area(v1, v2, v3):
    d = hinge_det(v1, v2, v3)
    return np.sqrt(max(d, 0.0))

def hbar_hinge(v1, v2, v3):
    """ħ_h = √det(G_h) / (4 ln 2)"""
    return hinge_area(v1, v2, v3) / (4 * np.log(2))

def holonomy(v1, v2, v3):
    """arg(G₁₂ G₂₃ G₃₁) — 게이지 플럭스"""
    g12 = np.vdot(v1, v2)
    g23 = np.vdot(v2, v3)
    g31 = np.vdot(v3, v1)
    return float(np.angle(g12 * g23 * g31))


# ═══════════════════════════════════════════════════════════════
#  ψ 벡터 생성
# ═══════════════════════════════════════════════════════════════

def make_S(direction, phase=0.0):
    """S 꼭짓점: C³(인덱스 2,3,4)에 집중, 작은 C² 성분."""
    psi = np.zeros(5, dtype=complex)
    psi[2 + direction] = np.exp(1j * phase)
    return normalize(psi)

def make_T(theta, phi, c3_leak=0.05):
    """T 꼭짓점: C²(인덱스 0,1)에 집중, 작은 C³ leak."""
    psi = np.zeros(5, dtype=complex)
    c2_amp = np.sqrt(1 - c3_leak**2)
    psi[0] = c2_amp * np.cos(theta) * np.exp(1j * phi)
    psi[1] = c2_amp * np.sin(theta)
    # C³ leak (균등 분배)
    psi[2] = c3_leak / np.sqrt(3)
    psi[3] = c3_leak / np.sqrt(3) * np.exp(1j * 0.3)
    psi[4] = c3_leak / np.sqrt(3) * np.exp(1j * 0.7)
    return normalize(psi)


# ═══════════════════════════════════════════════════════════════
#  원자별 심플렉스 구조
# ═══════════════════════════════════════════════════════════════

def build_atom(Z, name):
    """원자 = Z개 심플렉스, SSS 핵 공유.
    꼭짓점: S₁S₂S₃ (공유) + Z × (T_e, T_slot)
    """
    # SSS 핵 (직교 쿼크)
    vecs = {
        'S1': make_S(0),
        'S2': make_S(1),
        'S3': make_S(2),
    }

    # 각 심플렉스의 T 쌍 (전자 + 슬롯)
    for k in range(Z):
        theta_e = 0.3 + k * 0.4      # 전자마다 다른 C² 방향
        phi_e = k * np.pi / Z
        theta_s = theta_e + 0.8       # 슬롯은 전자와 다른 방향
        phi_s = phi_e + 0.5

        vecs[f'T{2*k+1}'] = make_T(theta_e, phi_e, c3_leak=0.05)
        vecs[f'T{2*k+2}'] = make_T(theta_s, phi_s, c3_leak=0.05)

    # 심플렉스 목록
    simplices = []
    for k in range(Z):
        simplices.append(('S1', 'S2', 'S3', f'T{2*k+1}', f'T{2*k+2}'))

    return vecs, simplices


def build_h2():
    """H₂ 분자: 2 심플렉스, T 꼭짓점 공유 (공유결합)."""
    vecs = {
        # 양성자 A
        'S1': make_S(0),
        'S2': make_S(1),
        'S3': make_S(2),
        # 양성자 B (약간 다른 위상)
        'S4': make_S(0, phase=0.1),
        'S5': make_S(1, phase=0.1),
        'S6': make_S(2, phase=0.1),
        # T 꼭짓점
        'T1': make_T(0.3, 0.0, c3_leak=0.05),     # 전자 A
        'T*': make_T(0.8, 0.3, c3_leak=0.08),      # 공유 (결합!)
        'T2': make_T(1.2, 0.5, c3_leak=0.05),      # 전자 B
    }
    simplices = [
        ('S1', 'S2', 'S3', 'T1', 'T*'),   # H atom A
        ('S4', 'S5', 'S6', 'T*', 'T2'),   # H atom B
    ]
    return vecs, simplices


# ═══════════════════════════════════════════════════════════════
#  분석 함수
# ═══════════════════════════════════════════════════════════════

def classify(name_triple, vecs):
    """힌지 분류: SSS/SST/STT/TTT"""
    n_s = sum(1 for n in name_triple if n.startswith('S'))
    return {3: 'SSS', 2: 'SST', 1: 'STT', 0: 'TTT'}[n_s]


def analyze_simplex(vecs, simplex, label=""):
    """단일 심플렉스의 모든 힌지를 분석."""
    results = {'SSS': [], 'SST': [], 'STT': [], 'TTT': []}

    for tri in combinations(simplex, 3):
        htype = classify(tri, vecs)
        v1, v2, v3 = vecs[tri[0]], vecs[tri[1]], vecs[tri[2]]
        det_val = hinge_det(v1, v2, v3)
        area = hinge_area(v1, v2, v3)
        hbar = hbar_hinge(v1, v2, v3)
        holo = holonomy(v1, v2, v3)

        results[htype].append({
            'vertices': tri,
            'det': det_val,
            'area': area,
            'hbar': hbar,
            'holonomy': holo,
        })

    return results


def print_analysis(name, vecs, simplices):
    """원자/분자의 전체 분석을 출력."""
    print(f"\n{'═' * 65}")
    print(f"  {name}")
    print(f"  꼭짓점 {len(vecs)}개, 심플렉스 {len(simplices)}개")
    print(f"{'═' * 65}")

    # Gram 행렬 (크기)
    keys = sorted(vecs.keys())
    n = len(keys)
    G = np.zeros((n, n), dtype=complex)
    for i in range(n):
        for j in range(n):
            G[i, j] = np.vdot(vecs[keys[i]], vecs[keys[j]])

    W = np.abs(G)**2 / 5  # real shadow

    print(f"\n  |G_ij| (overlap 크기):")
    header = "        " + "  ".join(f"{k:>6s}" for k in keys)
    print(header)
    for i, ki in enumerate(keys):
        row = f"  {ki:>5s} "
        for j, kj in enumerate(keys):
            row += f" {abs(G[i,j]):6.4f}"
        print(row)

    # 힌지 분석 (심플렉스별)
    all_hinges = {}  # 중복 제거용
    for s_idx, simp in enumerate(simplices):
        print(f"\n  심플렉스 {s_idx+1}: {simp}")
        results = analyze_simplex(vecs, simp)

        for htype in ['SSS', 'SST', 'STT', 'TTT']:
            if results[htype]:
                print(f"    {htype} 힌지 ({len(results[htype])}개):")
                for h in results[htype]:
                    tri_key = tuple(sorted(h['vertices']))
                    all_hinges[tri_key] = h
                    all_hinges[tri_key]['type'] = htype
                    print(f"      {h['vertices']}: det={h['det']:.6f}  "
                          f"A={h['area']:.6f}  ħ={h['hbar']:.6f}  "
                          f"Φ={h['holonomy']:+.4f}")

    # 요약 통계
    print(f"\n  {'─' * 55}")
    print(f"  요약:")

    sss = [h for h in all_hinges.values() if h['type'] == 'SSS']
    sst = [h for h in all_hinges.values() if h['type'] == 'SST']
    stt = [h for h in all_hinges.values() if h['type'] == 'STT']

    if sss:
        det_sss = np.mean([h['det'] for h in sss])
        print(f"    SSS (강력):   {len(sss)}개, ⟨det⟩ = {det_sss:.6f}")
    if sst:
        det_sst = np.mean([h['det'] for h in sst])
        print(f"    SST (전자기): {len(sst)}개, ⟨det⟩ = {det_sst:.6f}")
    if stt:
        det_stt = np.mean([h['det'] for h in stt])
        print(f"    STT (약력):   {len(stt)}개, ⟨det⟩ = {det_stt:.6f}")

    # 힘 비율
    if sss and sst:
        ratio_em_strong = np.mean([h['det'] for h in sst]) / np.mean([h['det'] for h in sss])
        print(f"\n    EM/Strong det 비 = {ratio_em_strong:.6f}")
        if stt:
            ratio_weak_strong = np.mean([h['det'] for h in stt]) / np.mean([h['det'] for h in sss])
            print(f"    Weak/Strong det 비 = {ratio_weak_strong:.6f}")

    # 총 Regge-like 양
    total_det = sum(h['det'] for h in all_hinges.values())
    total_area = sum(h['area'] for h in all_hinges.values())
    total_hbar = sum(h['hbar'] for h in all_hinges.values())
    n_hinges = len(all_hinges)
    print(f"\n    고유 힌지 수: {n_hinges}")
    print(f"    Σ det = {total_det:.6f}")
    print(f"    Σ A   = {total_area:.6f}")
    print(f"    Σ ħ   = {total_hbar:.6f}")

    # G 고유값
    eigvals = np.sort(np.linalg.eigvalsh(np.abs(G)**2 / 5))[::-1]
    print(f"\n    W = |G|²/5 고유값: {eigvals[:5]}")
    print(f"    rank(G) = {np.sum(np.linalg.eigvalsh(G.real) > 0.01)}")

    return all_hinges


# ═══════════════════════════════════════════════════════════════
#  실행
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    atoms = {}

    # 수소 (Z=1)
    vecs, simps = build_atom(1, "H")
    atoms['H'] = print_analysis("수소 (H) — 1 simplex", vecs, simps)

    # 헬륨 (Z=2)
    vecs, simps = build_atom(2, "He")
    atoms['He'] = print_analysis("헬륨 (He) — 2 simplices, SSS 공유", vecs, simps)

    # H₂ 분자
    vecs, simps = build_h2()
    atoms['H2'] = print_analysis("수소 분자 (H₂) — 2 simplices, T 공유 (결합)", vecs, simps)

    # 리튬 (Z=3)
    vecs, simps = build_atom(3, "Li")
    atoms['Li'] = print_analysis("리튬 (Li) — 3 simplices, SSS 공유", vecs, simps)

    # 베릴륨 (Z=4)
    vecs, simps = build_atom(4, "Be")
    atoms['Be'] = print_analysis("베릴륨 (Be) — 4 simplices, SSS 공유", vecs, simps)

    # ═══════════════════════════════════════════════════════════
    #  원자 간 비교
    # ═══════════════════════════════════════════════════════════

    print(f"\n{'═' * 65}")
    print(f"  원자 간 비교")
    print(f"{'═' * 65}")

    print(f"\n  {'원자':>6s} {'심플렉스':>8s} {'힌지수':>6s} {'Σdet':>10s} {'Σ면적':>10s} {'⟨SSS det⟩':>10s} {'⟨SST det⟩':>10s}")
    print(f"  {'─'*65}")
    for name in ['H', 'He', 'H2', 'Li', 'Be']:
        hinges = atoms[name]
        n_simp = {'H': 1, 'He': 2, 'H2': 2, 'Li': 3, 'Be': 4}[name]
        n_h = len(hinges)
        sum_det = sum(h['det'] for h in hinges.values())
        sum_area = sum(h['area'] for h in hinges.values())
        sss_det = np.mean([h['det'] for h in hinges.values() if h['type'] == 'SSS']) if any(h['type'] == 'SSS' for h in hinges.values()) else 0
        sst_det = np.mean([h['det'] for h in hinges.values() if h['type'] == 'SST']) if any(h['type'] == 'SST' for h in hinges.values()) else 0
        print(f"  {name:>6s} {n_simp:>8d} {n_h:>6d} {sum_det:>10.4f} {sum_area:>10.4f} {sss_det:>10.6f} {sst_det:>10.6f}")

    # Σdet 비율 (질량 비율의 proxy)
    print(f"\n  Σdet 비율 (vs H):")
    h_det = sum(h['det'] for h in atoms['H'].values())
    for name in ['H', 'He', 'H2', 'Li', 'Be']:
        ratio = sum(h['det'] for h in atoms[name].values()) / h_det
        z = {'H': 1, 'He': 2, 'H2': '1+1', 'Li': 3, 'Be': 4}[name]
        print(f"    {name}: Σdet/Σdet(H) = {ratio:.4f}  (Z = {z})")

    # 결과 저장
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043_Simplex_Anatomy.txt")
    # stdout을 파일에도 저장하려면 다시 실행해야 하지만,
    # 여기서는 요약만 저장
    with open(outfile, 'w') as f:
        f.write("EXP_043: Simplex Anatomy — Numerical Geometry of Atoms\n")
        f.write("=" * 55 + "\n\n")
        f.write("심플렉스 구조에서 직접 계산한 힌지 det, 면적, ħ\n\n")
        f.write(f"{'원자':>6s} {'심플렉스':>8s} {'힌지수':>6s} {'Σdet':>10s} {'⟨SSS⟩':>10s} {'⟨SST⟩':>10s}\n")
        for name in ['H', 'He', 'H2', 'Li', 'Be']:
            hinges = atoms[name]
            n_simp = {'H': 1, 'He': 2, 'H2': 2, 'Li': 3, 'Be': 4}[name]
            n_h = len(hinges)
            sum_det = sum(h['det'] for h in hinges.values())
            sss_det = np.mean([h['det'] for h in hinges.values() if h['type'] == 'SSS']) if any(h['type'] == 'SSS' for h in hinges.values()) else 0
            sst_det = np.mean([h['det'] for h in hinges.values() if h['type'] == 'SST']) if any(h['type'] == 'SST' for h in hinges.values()) else 0
            f.write(f"{name:>6s} {n_simp:>8d} {n_h:>6d} {sum_det:>10.4f} {sss_det:>10.6f} {sst_det:>10.6f}\n")
    print(f"\n결과 저장: {outfile}")
