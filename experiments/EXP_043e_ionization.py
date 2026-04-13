"""
EXP_043e: Ionization Energy from Simplex Topology
===================================================

가장 바깥 electron의 score = 1/(n+l)² ∝ ionization energy.
Shell 채움은 Madelung 순서 (EXP_043d에서 검증됨).

비교: DRLT score vs NIST 실측 IE (eV).
"""

import numpy as np
import os

print("=" * 70)
print("EXP_043e: Ionization Energy from 1/(n+l)²")
print("=" * 70)

# ═══════════════════════════════════════════════════════════════
#  Madelung filling order
# ═══════════════════════════════════════════════════════════════

n_T = 2

def orbital_capacity(l):
    return n_T * (2 * l + 1)

# Madelung order: sort by n+l, then by n
def madelung_orbitals(n_max=8):
    orbs = []
    for n in range(1, n_max + 1):
        for l in range(n):
            orbs.append((n, l, orbital_capacity(l)))
    orbs.sort(key=lambda x: (x[0] + x[1], x[0]))
    return orbs

def fill_electrons(Z):
    """Z개 전자를 Madelung 순서로 채움.
    Returns: list of (n, l, count_in_subshell)
    """
    orbs = madelung_orbitals()
    config = []
    remaining = Z
    for n, l, cap in orbs:
        if remaining <= 0:
            break
        filled = min(remaining, cap)
        config.append((n, l, filled))
        remaining -= filled
    return config

def outermost_score(Z):
    """가장 바깥 전자의 score = 1/(n+l)²."""
    config = fill_electrons(Z)
    if not config:
        return 0
    n, l, _ = config[-1]
    return 1.0 / (n + l)**2

def outermost_nl(Z):
    config = fill_electrons(Z)
    if not config:
        return 0, 0
    return config[-1][0], config[-1][1]


# ═══════════════════════════════════════════════════════════════
#  NIST Ionization Energies (eV) — 1st IE
# ═══════════════════════════════════════════════════════════════

NIST_IE = {
    1: 13.598, 2: 24.587, 3: 5.392, 4: 9.323, 5: 8.298,
    6: 11.260, 7: 14.534, 8: 13.618, 9: 17.423, 10: 21.565,
    11: 5.139, 12: 7.646, 13: 5.986, 14: 8.152, 15: 10.487,
    16: 10.360, 17: 12.968, 18: 15.760, 19: 4.341, 20: 6.113,
    21: 6.561, 22: 6.828, 23: 6.746, 24: 6.767, 25: 7.434,
    26: 7.902, 27: 7.881, 28: 7.640, 29: 7.726, 30: 9.394,
    31: 5.999, 32: 7.899, 33: 9.789, 34: 9.752, 35: 11.814,
    36: 14.000, 37: 4.177, 38: 5.695, 39: 6.217, 40: 6.634,
    41: 6.759, 42: 7.092, 43: 7.119, 44: 7.361, 45: 7.459,
    46: 8.337, 47: 7.576, 48: 8.994, 49: 5.786, 50: 7.344,
    51: 8.608, 52: 9.010, 53: 10.451, 54: 12.130,
    55: 3.894, 56: 5.212, 57: 5.577, 58: 5.539, 59: 5.473,
    60: 5.525, 61: 5.582, 62: 5.644, 63: 5.670, 64: 6.150,
    65: 5.864, 66: 5.939, 67: 6.022, 68: 6.108, 69: 6.184,
    70: 6.254, 71: 5.426, 72: 6.825, 73: 7.550, 74: 7.864,
    75: 7.833, 76: 8.438, 77: 8.967, 78: 8.959, 79: 9.226,
    80: 10.437, 81: 6.108, 82: 7.417, 83: 7.286, 84: 8.414,
    85: 9.318, 86: 10.749,
}

# ═══════════════════════════════════════════════════════════════
#  비교
# ═══════════════════════════════════════════════════════════════

elements = {
    1:'H', 2:'He', 3:'Li', 4:'Be', 5:'B', 6:'C', 7:'N', 8:'O',
    9:'F', 10:'Ne', 11:'Na', 12:'Mg', 13:'Al', 14:'Si', 15:'P',
    16:'S', 17:'Cl', 18:'Ar', 19:'K', 20:'Ca', 21:'Sc', 22:'Ti',
    23:'V', 24:'Cr', 25:'Mn', 26:'Fe', 27:'Co', 28:'Ni', 29:'Cu',
    30:'Zn', 31:'Ga', 32:'Ge', 33:'As', 34:'Se', 35:'Br', 36:'Kr',
    37:'Rb', 38:'Sr', 39:'Y', 40:'Zr', 41:'Nb', 42:'Mo', 43:'Tc',
    44:'Ru', 45:'Rh', 46:'Pd', 47:'Ag', 48:'Cd', 49:'In', 50:'Sn',
    51:'Sb', 52:'Te', 53:'I', 54:'Xe', 55:'Cs', 56:'Ba',
    79:'Au', 80:'Hg', 82:'Pb', 86:'Rn',
}

# Score 계산
scores = {}
for Z in range(1, 87):
    scores[Z] = outermost_score(Z)

# 비례 상수 결정: IE = k × score
# 최소자승법으로 k 결정
Zs = sorted(set(scores.keys()) & set(NIST_IE.keys()))
s_vals = np.array([scores[Z] for Z in Zs])
ie_vals = np.array([NIST_IE[Z] for Z in Zs])
k_fit = np.sum(s_vals * ie_vals) / np.sum(s_vals**2)

print(f"\n  비례 상수 k = {k_fit:.2f} eV (IE = k / (n+l)²)")
print(f"  참고: 수소 IE = 13.6 eV, k × 1/(1+0)² = k = {k_fit:.2f}")

# 출력
print(f"\n{'Z':>4s} {'Sym':>4s} {'n':>2s} {'l':>2s} {'n+l':>4s} "
      f"{'score':>8s} {'DRLT IE':>8s} {'NIST IE':>8s} {'err%':>7s}")
print("─" * 55)

errors = []
for Z in range(1, 87):
    if Z not in NIST_IE:
        continue
    n, l = outermost_nl(Z)
    sc = scores[Z]
    ie_drlt = k_fit * sc
    ie_nist = NIST_IE[Z]
    err = (ie_drlt - ie_nist) / ie_nist * 100
    errors.append(abs(err))
    sym = elements.get(Z, '')
    flag = ''
    if abs(err) < 10:
        flag = '✓'
    elif abs(err) > 50:
        flag = '✗'
    print(f"{Z:>4d} {sym:>4s} {n:>2d} {l:>2d} {n+l:>4d} "
          f"{sc:>8.4f} {ie_drlt:>8.2f} {ie_nist:>8.3f} {err:>+7.1f}% {flag}")

print(f"\n  평균 |오차|: {np.mean(errors):.1f}%")
print(f"  중앙값 |오차|: {np.median(errors):.1f}%")
print(f"  10% 이내: {sum(1 for e in errors if e < 10)}/{len(errors)}")
print(f"  20% 이내: {sum(1 for e in errors if e < 20)}/{len(errors)}")
print(f"  30% 이내: {sum(1 for e in errors if e < 30)}/{len(errors)}")

# ═══════════════════════════════════════════════════════════════
#  주기성 확인: 같은 n+l 내에서의 IE 변화
# ═══════════════════════════════════════════════════════════════

print(f"\n{'═' * 70}")
print("주기성: 같은 subshell 내 IE 변화 (score는 동일, IE는 변함)")
print(f"{'═' * 70}")

print("\n  같은 score인데 IE가 다른 원소들 (subshell 내 변동):")
# Group by (n, l)
from collections import defaultdict
by_subshell = defaultdict(list)
for Z in range(1, 87):
    if Z not in NIST_IE:
        continue
    config = fill_electrons(Z)
    n, l, count = config[-1]
    by_subshell[(n, l)].append((Z, NIST_IE[Z], count))

for (n, l), entries in sorted(by_subshell.items()):
    if len(entries) > 1:
        name = f"{n}{'spdf'[l]}"
        ie_list = [ie for _, ie, _ in entries]
        z_list = [z for z, _, _ in entries]
        sym_list = [elements.get(z, str(z)) for z in z_list]
        print(f"  {name}: {', '.join(f'{s}={ie:.1f}' for s, ie in zip(sym_list, ie_list))}")
        print(f"       range: {min(ie_list):.1f} - {max(ie_list):.1f} eV "
              f"(factor {max(ie_list)/min(ie_list):.2f}×)")

# ═══════════════════════════════════════════════════════════════
#  개선: subshell 내 count 보정
# ═══════════════════════════════════════════════════════════════

print(f"\n{'═' * 70}")
print("개선: IE = k/(n+l)² × f(count, capacity)")
print("  f = (count/capacity) — shell 채움 비율")
print(f"{'═' * 70}")

def improved_score(Z):
    """score에 subshell 채움 비율 보정."""
    config = fill_electrons(Z)
    if not config:
        return 0
    n, l, count = config[-1]
    cap = n_T * (2 * l + 1)
    base = 1.0 / (n + l)**2
    fill_fraction = count / cap
    return base * fill_fraction

# 새 k 결정
s2 = np.array([improved_score(Z) for Z in Zs])
k2 = np.sum(s2 * ie_vals) / np.sum(s2**2)

errors2 = []
print(f"\n  k = {k2:.2f} eV")
print(f"\n{'Z':>4s} {'Sym':>4s} {'(n,l,cnt)':>10s} {'score':>8s} {'DRLT':>8s} {'NIST':>8s} {'err%':>7s}")
print("─" * 60)
for Z in range(1, 87):
    if Z not in NIST_IE:
        continue
    config = fill_electrons(Z)
    n, l, count = config[-1]
    sc = improved_score(Z)
    ie_drlt = k2 * sc
    ie_nist = NIST_IE[Z]
    err = (ie_drlt - ie_nist) / ie_nist * 100
    errors2.append(abs(err))
    sym = elements.get(Z, '')
    flag = '✓' if abs(err) < 15 else ''
    print(f"{Z:>4d} {sym:>4s} ({n},{l},{count:>2d})   "
          f"{sc:>8.4f} {ie_drlt:>8.2f} {ie_nist:>8.3f} {err:>+7.1f}% {flag}")

print(f"\n  평균 |오차|: {np.mean(errors2):.1f}%")
print(f"  중앙값 |오차|: {np.median(errors2):.1f}%")
print(f"  15% 이내: {sum(1 for e in errors2 if e < 15)}/{len(errors2)}")
print(f"  30% 이내: {sum(1 for e in errors2 if e < 30)}/{len(errors2)}")

# 결과 저장
results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
outfile = os.path.join(results_dir, "EXP_043e_Ionization_Energy.txt")
with open(outfile, 'w') as f:
    f.write("EXP_043e: Ionization Energy from Simplex Topology\n")
    f.write("=" * 50 + "\n\n")
    f.write(f"Basic: IE = {k_fit:.2f} / (n+l)²\n")
    f.write(f"  Mean |error|: {np.mean(errors):.1f}%\n\n")
    f.write(f"Improved: IE = {k2:.2f} / (n+l)² × (count/capacity)\n")
    f.write(f"  Mean |error|: {np.mean(errors2):.1f}%\n")
print(f"\n결과 저장: {outfile}")
