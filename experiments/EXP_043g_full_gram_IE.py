"""
EXP_043g: Full Gram Matrix IE — Δdet = Ionization Energy
==========================================================

전체 원자의 (2Z+3)×(2Z+3) Gram 행렬을 구성하고,
가장 바깥 전자를 제거했을 때의 det 변화량으로 IE를 구한다.

Matrix structure:
  [S block 3×3]: I (직교 쿼크)
  [ST block 3×2Z]: 핵-전자 coupling ∝ 1/(n+l)
  [T block 2Z×2Z]: 전자-전자 overlap (shell 구조 반영)

IE ∝ log det(G_full) - log det(G_ionized)
"""

import numpy as np
import os

print("=" * 70)
print("EXP_043g: Full Gram Matrix IE — Δ(log det)")
print("=" * 70)

n_S = 3
n_T = 2
IE_H = 13.598  # eV


# ═══════════════════════════════════════════════════════════════
#  Madelung filling
# ═══════════════════════════════════════════════════════════════

def orbital_capacity(l):
    return n_T * (2 * l + 1)

def madelung_orbitals():
    orbs = []
    for n in range(1, 9):
        for l in range(n):
            orbs.append((n, l, orbital_capacity(l)))
    orbs.sort(key=lambda x: (x[0] + x[1], x[0]))
    return orbs

def fill_electrons(Z):
    orbs = madelung_orbitals()
    config = []  # list of (n, l, count)
    remaining = Z
    for n, l, cap in orbs:
        if remaining <= 0:
            break
        filled = min(remaining, cap)
        config.append((n, l, filled))
        remaining -= filled
    return config

def electron_list(Z):
    """Z개 전자의 (n, l, m_index) 목록."""
    config = fill_electrons(Z)
    elecs = []
    for n, l, count in config:
        for k in range(count):
            elecs.append((n, l, k))
    return elecs


# ═══════════════════════════════════════════════════════════════
#  Gram 행렬 구성
# ═══════════════════════════════════════════════════════════════

def make_psi_S(direction):
    """S vertex: C³에 집중."""
    psi = np.zeros(5)
    psi[2 + direction] = 1.0
    return psi

def make_psi_T(n, l, m_idx, c3_base=0.15):
    """T vertex: C²에 집중, c3_leak = c3_base/(n+l).

    C² 방향은 (n, l, m_idx)에 의해 결정.
    """
    golden = (1 + np.sqrt(5)) / 2
    global_idx = m_idx + 7 * n + 13 * l  # unique seed per orbital
    theta = np.pi * (global_idx + 0.5) / max(2*(2*l+1), 1)
    phi = 2 * np.pi * global_idx / golden + n * 1.0

    c3_leak = c3_base / (n + l)

    psi = np.zeros(5)
    c2_amp = np.sqrt(1 - c3_leak**2)
    psi[0] = c2_amp * np.cos(theta)
    psi[1] = c2_amp * np.sin(theta)
    # C³ leak: l에 따라 방향 배분
    if l == 0:
        psi[2] = c3_leak / np.sqrt(3)
        psi[3] = c3_leak / np.sqrt(3)
        psi[4] = c3_leak / np.sqrt(3)
    elif l == 1:
        psi[2 + (m_idx % 3)] = c3_leak  # 특정 C³ 방향 점유
    elif l == 2:
        psi[2 + (m_idx % 3)] = c3_leak * 0.7
        psi[2 + ((m_idx+1) % 3)] = c3_leak * 0.7
    else:
        psi[2] = c3_leak / np.sqrt(3)
        psi[3] = c3_leak / np.sqrt(3)
        psi[4] = c3_leak / np.sqrt(3)

    norm = np.linalg.norm(psi)
    return psi / norm if norm > 1e-15 else psi


def build_gram(Z, c3_base=0.15):
    """진짜 ψ 벡터로 Gram 행렬 구성. G = ΨΨᵀ (실수 모델).

    항상 PSD. 행/열 제거 시 det 감소 보장.
    """
    elecs = electron_list(Z)

    # 모든 ψ 벡터 수집
    psi_list = []
    # S vertices
    for d in range(3):
        psi_list.append(make_psi_S(d))

    # T vertices (electron + slot)
    for n, l, m in elecs:
        psi_list.append(make_psi_T(n, l, m, c3_base))
        # slot: 직교 방향
        psi_list.append(make_psi_T(n, l, m + 100, c3_base))

    Psi = np.array(psi_list)  # (2Z+3) × 5
    G = Psi @ Psi.T           # (2Z+3) × (2Z+3), PSD 보장

    return G


def compute_IE_gram(Z, c3_base=0.15):
    """전체 Gram 행렬에서 IE = Δ(log det) 계산.

    G = ΨΨᵀ (PSD). 전자 제거 = 행/열 삭제.
    Δlogdet = logdet(G_full) - logdet(G_ionized) > 0 항상.
    """
    if Z == 0:
        return 0, 0, 0

    G_full = build_gram(Z, c3_base)

    # Regularize: add tiny diagonal for numerical stability
    G_full += 1e-12 * np.eye(G_full.shape[0])

    sign_f, logdet_f = np.linalg.slogdet(G_full)

    # 가장 바깥 전자 제거 (마지막 2행/열)
    G_ion = G_full[:-2, :-2]
    sign_i, logdet_i = np.linalg.slogdet(G_ion)

    delta_logdet = logdet_f - logdet_i

    return delta_logdet, logdet_f, logdet_i


# ═══════════════════════════════════════════════════════════════
#  NIST data
# ═══════════════════════════════════════════════════════════════

NIST_IE = {
    1: 13.598, 2: 24.587, 3: 5.392, 4: 9.323, 5: 8.298,
    6: 11.260, 7: 14.534, 8: 13.618, 9: 17.423, 10: 21.565,
    11: 5.139, 12: 7.646, 13: 5.986, 14: 8.152, 15: 10.487,
    16: 10.360, 17: 12.968, 18: 15.760, 19: 4.341, 20: 6.113,
    21: 6.561, 22: 6.828, 23: 6.746, 24: 6.767, 25: 7.434,
    26: 7.902, 27: 7.881, 28: 7.640, 29: 7.726, 30: 9.394,
    31: 5.999, 32: 7.899, 33: 9.789, 34: 9.752, 35: 11.814,
    36: 14.000,
}

elements = {
    1:'H', 2:'He', 3:'Li', 4:'Be', 5:'B', 6:'C', 7:'N', 8:'O',
    9:'F', 10:'Ne', 11:'Na', 12:'Mg', 13:'Al', 14:'Si', 15:'P',
    16:'S', 17:'Cl', 18:'Ar', 19:'K', 20:'Ca', 21:'Sc', 22:'Ti',
    23:'V', 24:'Cr', 25:'Mn', 26:'Fe', 27:'Co', 28:'Ni', 29:'Cu',
    30:'Zn', 31:'Ga', 32:'Ge', 33:'As', 34:'Se', 35:'Br', 36:'Kr',
}


# ═══════════════════════════════════════════════════════════════
#  c3_base 최적화
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":

    # 먼저 c3_base를 스캔해서 H, He에 맞는 값 찾기
    print("\nc3_base 스캔 (H, He 기준):")
    print(f"{'k':>6s} {'Δld(H)':>8s} {'Δld(He)':>8s} {'ratio':>8s} {'NIST ratio':>10s}")
    print("─" * 48)
    for k10 in range(1, 20):
        k = k10 / 10.0
        dld_H, _, _ = compute_IE_gram(1, k)
        dld_He, _, _ = compute_IE_gram(2, k)
        if dld_H != 0:
            ratio = dld_He / dld_H
        else:
            ratio = 0
        nist_ratio = NIST_IE[2] / NIST_IE[1]
        print(f"{k:>6.1f} {dld_H:>8.4f} {dld_He:>8.4f} {ratio:>8.4f} {nist_ratio:>10.4f}")

    # 최적 k 찾기: IE_DRLT = scale × Δ(log det) → minimize error
    print(f"\n{'═' * 70}")
    print("최적 c3_base 탐색")
    print(f"{'═' * 70}")

    best_k = 0.3
    best_err = 1e10

    for k100 in range(5, 150):
        k = k100 / 100.0
        deltas = {}
        for Z in range(1, 37):
            dld, _, _ = compute_IE_gram(Z, k)
            deltas[Z] = dld

        # scale: IE = scale × Δld
        Zs = [Z for Z in range(1, 37) if Z in NIST_IE and deltas[Z] > 0]
        if not Zs:
            continue
        d_vals = np.array([deltas[Z] for Z in Zs])
        ie_vals = np.array([NIST_IE[Z] for Z in Zs])
        scale = np.sum(d_vals * ie_vals) / np.sum(d_vals**2)

        errors = [abs(scale * deltas[Z] - NIST_IE[Z]) / NIST_IE[Z] * 100
                  for Z in Zs]
        mean_err = np.mean(errors)
        if mean_err < best_err:
            best_err = mean_err
            best_k = k
            best_scale = scale

    print(f"  최적 k = {best_k:.2f}, scale = {best_scale:.2f}, mean |err| = {best_err:.1f}%")

    # 최적 k로 전체 계산
    print(f"\n{'═' * 70}")
    print(f"결과: k = {best_k}, IE = {best_scale:.2f} × Δ(log det)")
    print(f"{'═' * 70}")

    print(f"\n{'Z':>4s} {'Sym':>4s} {'outer':>5s} {'Δlogdet':>9s} "
          f"{'DRLT':>8s} {'NIST':>8s} {'err%':>7s}")
    print("─" * 55)

    all_errors = []
    for Z in range(1, 37):
        elecs = electron_list(Z)
        outer_orb = f"{elecs[-1][0]}{'spdf'[elecs[-1][1]]}" if elecs else "?"
        dld, ldf, ldi = compute_IE_gram(Z, best_k)
        ie_drlt = best_scale * dld
        ie_nist = NIST_IE.get(Z, 0)
        if ie_nist > 0:
            err = (ie_drlt - ie_nist) / ie_nist * 100
            all_errors.append(abs(err))
        else:
            err = 0
        sym = elements.get(Z, '')
        flag = '✓' if abs(err) < 20 else ''
        print(f"{Z:>4d} {sym:>4s} {outer_orb:>5s} {dld:>9.5f} "
              f"{ie_drlt:>8.2f} {ie_nist:>8.3f} {err:>+7.1f}% {flag}")

    print(f"\n  평균 |오차|: {np.mean(all_errors):.1f}%")
    print(f"  중앙값 |오차|: {np.median(all_errors):.1f}%")
    print(f"  20% 이내: {sum(1 for e in all_errors if e < 20)}/{len(all_errors)}")
    print(f"  30% 이내: {sum(1 for e in all_errors if e < 30)}/{len(all_errors)}")
    print(f"  50% 이내: {sum(1 for e in all_errors if e < 50)}/{len(all_errors)}")

    # 주기성 확인
    print(f"\n  Noble gas peaks?")
    for nz in [2, 10, 18, 36]:
        dld_before, _, _ = compute_IE_gram(nz - 1, best_k)
        dld_noble, _, _ = compute_IE_gram(nz, best_k)
        dld_after, _, _ = compute_IE_gram(nz + 1, best_k) if nz < 36 else (0,0,0)
        is_peak = dld_noble > dld_before and dld_noble > dld_after
        sym = elements.get(nz, '')
        print(f"    {sym} (Z={nz}): Δld = {dld_noble:.5f} "
              f"({'PEAK ✓' if is_peak else 'no peak'})")

    # 저장
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043g_Full_Gram_IE.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_043g: Full Gram Matrix IE\n")
        f.write(f"k = {best_k}, scale = {best_scale:.2f}\n")
        f.write(f"IE = {best_scale:.2f} × Δ(log det(G))\n\n")
        f.write(f"Mean |error|: {np.mean(all_errors):.1f}%\n")
        f.write(f"Within 20%: {sum(1 for e in all_errors if e<20)}/{len(all_errors)}\n")
        f.write(f"Within 30%: {sum(1 for e in all_errors if e<30)}/{len(all_errors)}\n")
    print(f"\n결과 저장: {outfile}")
