"""
EXP_043d: Aufbau from Simplex — Does Madelung Rule Emerge?
===========================================================

Key idea (from the author):
  l quantum number = C³ contamination of T vertex.
  l=0 (s): pure C². l=1 (p): 1 C³ direction. l=2 (d): 2 C³ directions.

  Competition:
    3d: close (D=1/9) but dirty (l=2, C³ big)
    4s: far (D=1/16) but clean (l=0, pure C²)

  STT det ∝ D(n) × temporal_purity(l)
           = (1/n²) × (1 - l/n_S)^p   for some power p

  Greedy fill: highest STT det first.
  If this reproduces n+l ordering → Madelung from topology!
"""

import numpy as np
from itertools import combinations

print("=" * 70)
print("EXP_043d: Aufbau Principle from Simplex Topology")
print("=" * 70)

n_S = 3   # spatial dimension
n_T = 2   # temporal dimension


# ═══════════════════════════════════════════════════════════════
#  Orbital 정의
# ═══════════════════════════════════════════════════════════════

def orbital_capacity(l):
    """각 (n,l) subshell의 용량 = n_T × (2l+1)."""
    return n_T * (2 * l + 1)

def generate_orbitals(n_max=8):
    """모든 (n, l) orbital을 생성."""
    orbitals = []
    for n in range(1, n_max + 1):
        for l in range(n):  # l = 0, 1, ..., n-1
            cap = orbital_capacity(l)
            orbitals.append({
                'n': n, 'l': l,
                'name': f"{n}{'spdfghij'[l]}",
                'capacity': cap,
                'n_plus_l': n + l,
            })
    return orbitals


# ═══════════════════════════════════════════════════════════════
#  STT det 계산 — 여러 공식 시도
# ═══════════════════════════════════════════════════════════════

def stt_score_v1(n, l):
    """D(n) × (1 - l/n_S)²"""
    return (1.0 / n**2) * (1.0 - l / n_S)**2

def stt_score_v2(n, l):
    """D(n) × (1 - l/n_S)"""
    return (1.0 / n**2) * (1.0 - l / n_S)

def stt_score_v3(n, l):
    """1 / (n + l)²  — pure Madelung"""
    return 1.0 / (n + l)**2

def stt_score_v4(n, l):
    """D(n) × (1 - l²/n_S²)  — quadratic l"""
    return (1.0 / n**2) * (1.0 - (l / n_S)**2)

def stt_score_v5(n, l):
    """D(n) × (n_S - l) / n_S  — same as v2 actually"""
    return (1.0 / n**2) * (n_S - l) / n_S


# ═══════════════════════════════════════════════════════════════
#  Greedy filling
# ═══════════════════════════════════════════════════════════════

def greedy_fill(orbitals, score_fn, Z_max=118):
    """STT det이 높은 orbital부터 채움."""
    # 점수 계산
    for orb in orbitals:
        orb['score'] = score_fn(orb['n'], orb['l'])

    # 점수 순 정렬 (높은 것 먼저, 동점이면 낮은 n 먼저)
    sorted_orbs = sorted(orbitals, key=lambda o: (-o['score'], o['n']))

    # 채우기
    filling_order = []
    total = 0
    for orb in sorted_orbs:
        if total >= Z_max:
            break
        filling_order.append(orb)
        total += orb['capacity']

    return filling_order


# ═══════════════════════════════════════════════════════════════
#  Madelung 비교
# ═══════════════════════════════════════════════════════════════

# 실제 Madelung 순서
MADELUNG_ORDER = [
    '1s', '2s', '2p', '3s', '3p', '4s', '3d', '4p', '5s', '4d',
    '5p', '6s', '4f', '5d', '6p', '7s', '5f', '6d', '7p', '8s',
]

def compare_with_madelung(filling_order):
    """DRLT filling vs Madelung."""
    drlt_order = [o['name'] for o in filling_order]
    mad_order = MADELUNG_ORDER[:len(drlt_order)]

    matches = 0
    for i, (d, m) in enumerate(zip(drlt_order, mad_order)):
        match = '✓' if d == m else '✗'
        if d == m:
            matches += 1

    return matches, len(drlt_order), drlt_order, mad_order


# ═══════════════════════════════════════════════════════════════
#  실행
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    orbitals = generate_orbitals(n_max=8)

    # 먼저 각 orbital의 점수 비교표
    print(f"\n{'Orbital':>7s} {'n':>3s} {'l':>3s} {'n+l':>4s} {'cap':>4s} "
          f"{'v1: 1/n²(1-l/3)²':>17s} {'v2: 1/n²(1-l/3)':>16s} {'v3: 1/(n+l)²':>13s}")
    print("─" * 75)

    key_orbitals = [(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(3,2),(4,1),(5,0),
                    (4,2),(5,1),(6,0),(4,3),(5,2),(6,1),(7,0),(5,3),(6,2),(7,1)]
    for n, l in key_orbitals:
        name = f"{n}{'spdfghij'[l]}"
        cap = orbital_capacity(l)
        s1 = stt_score_v1(n, l)
        s2 = stt_score_v2(n, l)
        s3 = stt_score_v3(n, l)
        print(f"{name:>7s} {n:>3d} {l:>3d} {n+l:>4d} {cap:>4d} "
              f"{s1:>17.6f} {s2:>16.6f} {s3:>13.6f}")

    # 각 공식별 filling order 비교
    formulas = {
        'v1: 1/n²(1-l/3)²': stt_score_v1,
        'v2: 1/n²(1-l/3)':  stt_score_v2,
        'v3: 1/(n+l)²':     stt_score_v3,
        'v4: 1/n²(1-l²/9)': stt_score_v4,
    }

    print(f"\n{'═' * 70}")
    print("Filling Order 비교 (Madelung vs DRLT)")
    print(f"{'═' * 70}")

    for fname, ffunc in formulas.items():
        orbs = generate_orbitals(n_max=8)
        filling = greedy_fill(orbs, ffunc)
        matches, total, drlt, mad = compare_with_madelung(filling)

        print(f"\n  {fname}:")
        print(f"  DRLT:     {' → '.join(drlt[:15])}")
        print(f"  Madelung: {' → '.join(mad[:15])}")
        print(f"  일치: {matches}/{total}")

        # 상세 비교
        mismatches = []
        for i, (d, m) in enumerate(zip(drlt, mad)):
            if d != m:
                mismatches.append(f"#{i+1}: DRLT={d}, Mad={m}")
        if mismatches:
            print(f"  불일치: {', '.join(mismatches[:5])}")

    # ═══════════════════════════════════════════════════════════
    #  최적 공식 탐색
    # ═══════════════════════════════════════════════════════════

    print(f"\n{'═' * 70}")
    print("최적 power p 탐색: score = 1/n² × (1 - l/3)^p")
    print(f"{'═' * 70}")

    best_p = 0
    best_matches = 0
    for p_10 in range(1, 50):  # p from 0.1 to 5.0
        p = p_10 / 10.0

        def score_p(n, l, power=p):
            return (1.0 / n**2) * max(1.0 - l / n_S, 0.0)**power

        orbs = generate_orbitals(n_max=8)
        filling = greedy_fill(orbs, score_p)
        matches, total, drlt, mad = compare_with_madelung(filling)

        if matches > best_matches:
            best_matches = matches
            best_p = p
            print(f"  p = {p:.1f}: {matches}/{total} 일치  "
                  f"{'→'.join(drlt[:10])}")

    print(f"\n  최적: p = {best_p}, {best_matches} 일치")

    # ═══════════════════════════════════════════════════════════
    #  Shell 닫힘에서의 원소 배정
    # ═══════════════════════════════════════════════════════════

    print(f"\n{'═' * 70}")
    print("원소 배정 (최적 공식으로)")
    print(f"{'═' * 70}")

    elements = {
        1:'H', 2:'He', 3:'Li', 4:'Be', 5:'B', 6:'C', 7:'N', 8:'O',
        9:'F', 10:'Ne', 11:'Na', 12:'Mg', 13:'Al', 14:'Si', 15:'P',
        16:'S', 17:'Cl', 18:'Ar', 19:'K', 20:'Ca', 21:'Sc', 26:'Fe',
        29:'Cu', 30:'Zn', 36:'Kr', 54:'Xe', 86:'Rn',
    }

    def score_best(n, l):
        return (1.0 / n**2) * max(1.0 - l / n_S, 0.0)**best_p

    orbs = generate_orbitals(n_max=8)
    filling = greedy_fill(orbs, score_best, Z_max=120)

    Z = 0
    print(f"\n  {'Orbital':>7s} {'cap':>4s} {'Z range':>12s} {'Noble gas?':>12s}")
    print(f"  {'─' * 45}")
    for orb in filling:
        z_start = Z + 1
        Z += orb['capacity']
        z_end = Z
        sym_end = elements.get(z_end, '')
        noble = '← NOBLE' if sym_end in ['He','Ne','Ar','Kr','Xe','Rn'] else ''
        print(f"  {orb['name']:>7s} {orb['capacity']:>4d}   Z={z_start:>3d}-{z_end:>3d}  "
              f"{sym_end:>4s} {noble}")

    # 결과 저장
    import os
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043d_Madelung.txt")
    with open(outfile, 'w') as f:
        f.write(f"EXP_043d: Aufbau from Simplex Topology\n")
        f.write(f"Score = 1/n² × (1 - l/3)^p, p = {best_p}\n")
        f.write(f"Madelung match: {best_matches} orbitals\n\n")
        f.write(f"DRLT filling: {' → '.join([o['name'] for o in filling[:20]])}\n")
        f.write(f"Madelung:     {' → '.join(MADELUNG_ORDER[:20])}\n")
    print(f"\n결과 저장: {outfile}")
