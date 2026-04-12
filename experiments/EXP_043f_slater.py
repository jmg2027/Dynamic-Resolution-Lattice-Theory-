"""
EXP_043f: Slater Rules from Simplex — IE with STT Shielding
=============================================================

σ(j→i) = STT_det(i,j) / SST_det(i, nucleus)
Z_eff = Z - Σ_j σ(j→i)
IE = Z_eff² / (n+l)² × 13.6 eV / n_T

No new physics. Just re-reading the det matrix.
"""

import numpy as np
import os

print("=" * 70)
print("EXP_043f: Slater Rules from Simplex Geometry")
print("=" * 70)

n_S = 3
n_T = 2
IE_H = 13.598  # eV (hydrogen IE = m_e α² / 2)


# ═══════════════════════════════════════════════════════════════
#  Vertex construction (same as EXP_043c)
# ═══════════════════════════════════════════════════════════════

def normalize(v):
    return v / np.linalg.norm(v)

def make_S(direction):
    psi = np.zeros(5, dtype=complex)
    psi[2 + direction] = 1.0
    return psi

def make_T(theta, phi, c3_leak):
    psi = np.zeros(5, dtype=complex)
    c2_amp = np.sqrt(1 - c3_leak**2)
    psi[0] = c2_amp * np.cos(theta) * np.exp(1j * phi)
    psi[1] = c2_amp * np.sin(theta)
    psi[2] = c3_leak / np.sqrt(3) * np.exp(1j * 0.1)
    psi[3] = c3_leak / np.sqrt(3) * np.exp(1j * 0.3)
    psi[4] = c3_leak / np.sqrt(3) * np.exp(1j * 0.7)
    return normalize(psi)

def hinge_det(v1, v2, v3):
    G = np.array([
        [np.vdot(v1,v1), np.vdot(v1,v2), np.vdot(v1,v3)],
        [np.vdot(v2,v1), np.vdot(v2,v2), np.vdot(v2,v3)],
        [np.vdot(v3,v1), np.vdot(v3,v2), np.vdot(v3,v3)],
    ])
    return float(np.real(np.linalg.det(G)))


# ═══════════════════════════════════════════════════════════════
#  Madelung filling + shell-aware T vertices
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
    config = []
    remaining = Z
    for n, l, cap in orbs:
        if remaining <= 0:
            break
        filled = min(remaining, cap)
        config.append((n, l, filled))
        remaining -= filled
    return config


def build_atom_full(Z, c3_base=0.15):
    """원자를 만들고 모든 electron의 T vector를 반환.

    Returns:
        S: list of 3 S vectors
        electrons: list of dicts {n, l, idx_in_subshell, T_vec, T_slot_vec}
    """
    S = [make_S(0), make_S(1), make_S(2)]
    config = fill_electrons(Z)

    electrons = []
    golden = (1 + np.sqrt(5)) / 2

    global_idx = 0
    for n, l, count in config:
        c3_leak = c3_base * (1.0 / (n + l))  # coupling ∝ 1/(n+l)

        for k in range(count):
            theta_e = np.pi * (k + 0.5) / max(count, 1)
            phi_e = 2 * np.pi * global_idx / golden

            T_e = make_T(theta_e, phi_e, c3_leak)
            T_slot = make_T(np.pi - theta_e, phi_e + np.pi/3, c3_leak)

            electrons.append({
                'n': n, 'l': l, 'k': k,
                'T': T_e, 'T_slot': T_slot,
                'orbital': f"{n}{'spdf'[l]}",
            })
            global_idx += 1

    return S, electrons


# ═══════════════════════════════════════════════════════════════
#  Shielding calculation
# ═══════════════════════════════════════════════════════════════

def compute_IE(Z, c3_base=0.15):
    """각 전자의 Z_eff와 IE를 계산."""
    S, electrons = build_atom_full(Z, c3_base)

    if not electrons:
        return []

    n_e = len(electrons)

    # 각 전자의 SST det (nucleus coupling)
    sst_dets = []
    for i, e in enumerate(electrons):
        # 평균 SST det: 3개 S vertex pair × T_i
        dets = []
        for a, b in [(0,1), (0,2), (1,2)]:
            dets.append(hinge_det(S[a], S[b], e['T']))
        sst_dets.append(np.mean(dets))

    # 전자 쌍별 STT det (shielding)
    stt_matrix = np.zeros((n_e, n_e))
    for i in range(n_e):
        for j in range(n_e):
            if i == j:
                continue
            # STT det: S_avg, T_i, T_j
            dets = []
            for s in range(3):
                dets.append(hinge_det(S[s], electrons[i]['T'], electrons[j]['T']))
            stt_matrix[i, j] = np.mean(dets)

    # Z_eff for each electron
    results = []
    for i, e in enumerate(electrons):
        # σ(j→i) = STT_det(i,j) / SST_det(i)
        sigma_total = 0.0
        for j in range(n_e):
            if j == i:
                continue
            sigma = stt_matrix[i, j] / max(sst_dets[i], 1e-10)
            sigma_total += sigma

        z_eff = Z - sigma_total
        z_eff = max(z_eff, 0.1)  # prevent negative

        n_eff = e['n'] + e['l']  # effective quantum number
        ie = z_eff**2 / n_eff**2 * IE_H

        results.append({
            'n': e['n'], 'l': e['l'], 'k': e['k'],
            'orbital': e['orbital'],
            'sst_det': sst_dets[i],
            'sigma_total': sigma_total,
            'z_eff': z_eff,
            'ie': ie,
        })

    return results


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
#  실행
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":

    print(f"\n{'Z':>4s} {'Sym':>4s} {'outer':>5s} {'Z_eff':>6s} {'Σσ':>6s} "
          f"{'DRLT':>8s} {'NIST':>8s} {'err%':>7s}")
    print("─" * 58)

    all_errors = []
    all_results = {}

    for Z in range(1, 37):
        res = compute_IE(Z)
        if not res:
            continue

        # 가장 바깥 전자 (마지막)
        outer = res[-1]
        ie_drlt = outer['ie']
        ie_nist = NIST_IE.get(Z, 0)

        if ie_nist > 0:
            err = (ie_drlt - ie_nist) / ie_nist * 100
            all_errors.append(abs(err))
        else:
            err = 0

        sym = elements.get(Z, '')
        flag = '✓' if abs(err) < 20 else ''
        print(f"{Z:>4d} {sym:>4s} {outer['orbital']:>5s} "
              f"{outer['z_eff']:>6.2f} {outer['sigma_total']:>6.2f} "
              f"{ie_drlt:>8.2f} {ie_nist:>8.3f} {err:>+7.1f}% {flag}")

        all_results[Z] = res

    print(f"\n  평균 |오차|: {np.mean(all_errors):.1f}%")
    print(f"  중앙값 |오차|: {np.median(all_errors):.1f}%")
    print(f"  20% 이내: {sum(1 for e in all_errors if e < 20)}/{len(all_errors)}")
    print(f"  30% 이내: {sum(1 for e in all_errors if e < 30)}/{len(all_errors)}")
    print(f"  50% 이내: {sum(1 for e in all_errors if e < 50)}/{len(all_errors)}")

    # ═══════════════════════════════════════════════════════════
    #  Slater 상수 추출
    # ═══════════════════════════════════════════════════════════

    print(f"\n{'═' * 70}")
    print("Slater 차폐 상수 추출 (σ per electron pair)")
    print(f"{'═' * 70}")

    # He에서 1s-1s 차폐
    if 2 in all_results:
        res = all_results[2]
        sigma_1s = res[0]['sigma_total']  # electron 0이 electron 1에게 받는 차폐
        print(f"\n  He (1s²): σ(1s←1s) = {sigma_1s:.4f}")
        print(f"  Slater 경험값: 0.30")

    # Li에서 1s→2s 차폐
    if 3 in all_results:
        res = all_results[3]
        sigma_2s = res[2]['sigma_total']  # 2s electron의 총 차폐
        print(f"\n  Li (1s²2s¹): Σσ(2s) = {sigma_2s:.4f} (from 2 inner electrons)")
        print(f"  σ per inner = {sigma_2s/2:.4f}")
        print(f"  Slater 경험값: 0.85 per inner 1s electron")

    # Na에서 차폐
    if 11 in all_results:
        res = all_results[11]
        outer = res[-1]
        print(f"\n  Na (3s¹): Z_eff = {outer['z_eff']:.2f}, Σσ = {outer['sigma_total']:.2f}")
        print(f"  Slater Z_eff: 11 - 8×0.85 - 2×1.00 = 2.20")

    # 결과 저장
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043f_Slater_IE.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_043f: Slater Rules from Simplex — IE with STT Shielding\n")
        f.write("=" * 55 + "\n\n")
        f.write("σ(j→i) = STT_det(i,j) / SST_det(i)\n")
        f.write("Z_eff = Z - Σσ\n")
        f.write(f"IE = Z_eff² / (n+l)² × {IE_H:.3f} / {n_T}\n\n")
        f.write(f"Mean |error|: {np.mean(all_errors):.1f}%\n")
        f.write(f"Within 20%: {sum(1 for e in all_errors if e<20)}/{len(all_errors)}\n")
        f.write(f"Within 30%: {sum(1 for e in all_errors if e<30)}/{len(all_errors)}\n")
    print(f"\n결과 저장: {outfile}")
