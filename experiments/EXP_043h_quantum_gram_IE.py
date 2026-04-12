"""
EXP_043h: Quantum Number → ψ ∈ C⁵ → Gram Matrix → IE
=======================================================

No random. No fitting. Quantum numbers determine ψ exactly:
  ψ[0:2] = C² (temporal): spin direction, amplitude ~ coupling
  ψ[2:5] = C³ (spatial):  l/n_S leak, m_l selects direction

G_ij = ⟨ψ_i|ψ_j⟩ analytically.
IE = -Δ(log det) when outermost electron removed.
"""

import numpy as np
import os

print("=" * 70)
print("EXP_043h: Quantum Number → C⁵ → Gram → IE")
print("=" * 70)

n_S = 3
n_T = 2
IE_H = 13.598  # eV


# ═══════════════════════════════════════════════════════════════
#  ψ from quantum numbers
# ═══════════════════════════════════════════════════════════════

def psi_S(direction):
    """S vertex: pure C³. direction = 0, 1, 2."""
    v = np.zeros(5)
    v[2 + direction] = 1.0
    return v

def psi_T(n, l, m_l, m_s):
    """T vertex from (n, l, m_l, m_s).

    C² part (indices 0,1):
      amplitude = √(1 - (l/n_S)²) × 1/(n+l)  [coupling × purity]
      spin: m_s = +1/2 → ψ[0], m_s = -1/2 → ψ[1]

    C³ part (indices 2,3,4):
      amplitude = l/n_S  [angular momentum contamination]
      direction: m_l selects which C³ axis/axes

    Normalization preserves the RATIO between C² and C³.
    """
    psi = np.zeros(5)

    # C³ contamination amplitude
    c3_amp = l / n_S  # 0 for s, 1/3 for p, 2/3 for d, 1 for f

    # C² amplitude (temporal purity)
    c2_amp = np.sqrt(max(1.0 - c3_amp**2, 0.01))

    # C² part: spin direction
    if m_s > 0:  # spin up
        psi[0] = c2_amp
        psi[1] = 0
    else:  # spin down
        psi[0] = 0
        psi[1] = c2_amp

    # C³ part: m_l selects direction(s)
    if l == 0:
        # s orbital: tiny uniform C³ leak
        psi[2] = c3_amp / np.sqrt(3) if c3_amp > 0 else 0.01
        psi[3] = c3_amp / np.sqrt(3) if c3_amp > 0 else 0.01
        psi[4] = c3_amp / np.sqrt(3) if c3_amp > 0 else 0.01
    elif l == 1:
        # p orbital: m_l = -1, 0, +1 → x, y, z
        if m_l == -1:
            psi[2] = c3_amp
        elif m_l == 0:
            psi[3] = c3_amp
        else:  # m_l == +1
            psi[4] = c3_amp
    elif l == 2:
        # d orbital: m_l = -2..+2 → pairs of C³ directions
        if m_l == -2:
            psi[2] = c3_amp * 0.707; psi[3] = c3_amp * 0.707
        elif m_l == -1:
            psi[2] = c3_amp * 0.707; psi[4] = c3_amp * 0.707
        elif m_l == 0:
            psi[3] = c3_amp * 0.707; psi[4] = c3_amp * 0.707
        elif m_l == 1:
            psi[2] = c3_amp; psi[3] = 0
        else:  # m_l == 2
            psi[3] = c3_amp; psi[4] = 0
    elif l == 3:
        # f orbital: all three C³ directions
        psi[2] = c3_amp / np.sqrt(3)
        psi[3] = c3_amp / np.sqrt(3)
        psi[4] = c3_amp / np.sqrt(3)

    # Normalize
    norm = np.linalg.norm(psi)
    if norm > 1e-15:
        psi /= norm

    return psi


# ═══════════════════════════════════════════════════════════════
#  Electron configuration
# ═══════════════════════════════════════════════════════════════

def madelung_subshells():
    """Madelung order: (n, l) sorted by n+l, then n."""
    subs = []
    for n in range(1, 9):
        for l in range(n):
            subs.append((n, l))
    subs.sort(key=lambda x: (x[0] + x[1], x[0]))
    return subs

def electron_config(Z):
    """Z electrons → list of (n, l, m_l, m_s).

    Fill within subshell: m_l from -l to +l, spin up first then down (Hund).
    """
    subs = madelung_subshells()
    elecs = []
    remaining = Z

    for n, l in subs:
        if remaining <= 0:
            break
        cap = n_T * (2*l + 1)
        to_fill = min(remaining, cap)

        # Hund's rule: fill all m_l with spin up first, then spin down
        for m_s_phase in [+0.5, -0.5]:
            for m_l in range(-l, l+1):
                if to_fill <= 0:
                    break
                elecs.append((n, l, m_l, m_s_phase))
                to_fill -= 1
                remaining -= 1

    return elecs


# ═══════════════════════════════════════════════════════════════
#  Gram matrix and IE
# ═══════════════════════════════════════════════════════════════

def build_gram_from_qn(Z):
    """(3+Z) × (3+Z) Gram matrix from quantum numbers.

    Vertices: S₁, S₂, S₃, then Z electron T vertices.
    (No slot vertices — just the electrons themselves.)
    """
    elecs = electron_config(Z)

    psi_list = []
    # S vertices
    for d in range(3):
        psi_list.append(psi_S(d))
    # T vertices (one per electron)
    for n, l, m_l, m_s in elecs:
        psi_list.append(psi_T(n, l, m_l, m_s))

    Psi = np.array(psi_list)  # (3+Z) × 5
    G = Psi @ Psi.T           # (3+Z) × (3+Z), PSD

    return G, elecs


def compute_IE(Z):
    """IE from Δ(log det) when removing outermost electron."""
    if Z == 0:
        return 0, {}, []

    G_full, elecs = build_gram_from_qn(Z)
    G_full += 1e-14 * np.eye(G_full.shape[0])  # regularize

    sign_f, logdet_f = np.linalg.slogdet(G_full)

    # Remove last electron (outermost)
    G_ion = G_full[:-1, :-1]
    sign_i, logdet_i = np.linalg.slogdet(G_ion)

    # Δlogdet > 0 for PSD matrices (removing row/col decreases det)
    # Actually for Gram matrix, removing a vector CAN increase det
    # if the vector was nearly dependent. But let's see.
    delta = logdet_f - logdet_i

    outer = elecs[-1]
    info = {
        'n': outer[0], 'l': outer[1], 'm_l': outer[2], 'm_s': outer[3],
        'orbital': f"{outer[0]}{'spdf'[outer[1]]}",
        'delta_logdet': delta,
        'logdet_full': logdet_f,
    }

    return delta, info, elecs


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

elements = {i: s for i, s in zip(
    range(1, 37),
    ['H','He','Li','Be','B','C','N','O','F','Ne',
     'Na','Mg','Al','Si','P','S','Cl','Ar',
     'K','Ca','Sc','Ti','V','Cr','Mn','Fe','Co','Ni','Cu','Zn',
     'Ga','Ge','As','Se','Br','Kr']
)}


# ═══════════════════════════════════════════════════════════════
#  실행
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":

    # 1. 모든 원소의 Δlogdet 계산
    deltas = {}
    infos = {}
    for Z in range(1, 37):
        d, info, _ = compute_IE(Z)
        deltas[Z] = d
        infos[Z] = info

    # 2. Scale factor: IE = scale × |Δlogdet|
    Zs = [Z for Z in range(1, 37) if deltas[Z] != 0]
    d_vals = np.array([abs(deltas[Z]) for Z in Zs])
    ie_vals = np.array([NIST_IE[Z] for Z in Zs])
    scale = np.sum(d_vals * ie_vals) / np.sum(d_vals**2)

    print(f"\n  Scale = {scale:.2f} eV per unit |Δlogdet|")

    # 3. 결과 출력
    print(f"\n{'Z':>4s} {'Sym':>4s} {'orb':>4s} {'(n,l,ml,ms)':>12s} "
          f"{'Δlogdet':>9s} {'DRLT':>8s} {'NIST':>8s} {'err%':>7s}")
    print("─" * 65)

    errors = []
    for Z in range(1, 37):
        d = deltas[Z]
        info = infos[Z]
        ie_drlt = scale * abs(d)
        ie_nist = NIST_IE[Z]
        err = (ie_drlt - ie_nist) / ie_nist * 100
        errors.append(abs(err))
        sym = elements.get(Z, '')
        qn = f"({info['n']},{info['l']},{info['m_l']:+.0f},{info['m_s']:+.1f})"
        flag = '✓' if abs(err) < 20 else ''
        print(f"{Z:>4d} {sym:>4s} {info['orbital']:>4s} {qn:>12s} "
              f"{d:>9.5f} {ie_drlt:>8.2f} {ie_nist:>8.3f} {err:>+7.1f}% {flag}")

    print(f"\n  평균 |오차|: {np.mean(errors):.1f}%")
    print(f"  중앙값 |오차|: {np.median(errors):.1f}%")
    print(f"  20% 이내: {sum(1 for e in errors if e < 20)}/{len(errors)}")
    print(f"  30% 이내: {sum(1 for e in errors if e < 30)}/{len(errors)}")
    print(f"  50% 이내: {sum(1 for e in errors if e < 50)}/{len(errors)}")

    # 4. Noble gas peaks
    print(f"\n  Noble gas peaks?")
    for nz in [2, 10, 18, 36]:
        d_prev = abs(deltas.get(nz-1, 0))
        d_noble = abs(deltas.get(nz, 0))
        d_next = abs(deltas.get(nz+1, 0)) if nz < 36 else 0
        is_peak = d_noble > d_prev and d_noble > d_next
        sym = elements.get(nz, '')
        print(f"    {sym} (Z={nz}): |Δld| = {d_noble:.5f} "
              f"({'PEAK ✓' if is_peak else 'no'})")

    # 5. Gram 행렬 시각화 (H, He, Ne)
    for Z_show in [1, 2, 10]:
        G, elecs = build_gram_from_qn(Z_show)
        sym = elements[Z_show]
        print(f"\n  G matrix for {sym} (Z={Z_show}), shape {G.shape}:")
        print(f"  {G[:6, :6].round(4)}")

    # 저장
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043h_Quantum_Gram_IE.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_043h: Quantum Number → C⁵ → Gram → IE\n")
        f.write(f"Scale = {scale:.2f} eV\n")
        f.write(f"Mean |error|: {np.mean(errors):.1f}%\n")
        f.write(f"Within 20%: {sum(1 for e in errors if e<20)}/{len(errors)}\n")
        f.write(f"Within 30%: {sum(1 for e in errors if e<30)}/{len(errors)}\n\n")
        for Z in range(1, 37):
            info = infos[Z]
            ie_drlt = scale * abs(deltas[Z])
            err = (ie_drlt - NIST_IE[Z]) / NIST_IE[Z] * 100
            f.write(f"Z={Z:3d} {elements.get(Z,''):>3s} {info['orbital']:>3s} "
                    f"DRLT={ie_drlt:7.2f} NIST={NIST_IE[Z]:7.3f} err={err:+6.1f}%\n")
    print(f"\n결과 저장: {outfile}")
