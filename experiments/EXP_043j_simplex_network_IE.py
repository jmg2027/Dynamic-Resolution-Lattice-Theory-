"""
EXP_043j: Simplex Network IE — Full C⁵ vectors, proper geometry
================================================================

Each atom = Z simplices sharing SSS core.
Each simplex: {S₁, S₂, S₃, T_electron, T_slot}

ψ ∈ C⁵ constructed from quantum numbers:
  C² part: amplitude √(1 - c3²), direction from (n, m_s)
  C³ part: amplitude √α_GUT / n, direction from (l, m_l)

IE = log det(G_full) - log det(G_ionized)
   = "시공간 부피 변화" when outermost electron removed

Key fix from previous attempts:
  - Use COMPLEX vectors (not real) for proper C⁵ geometry
  - Include slot vertices (det > 0 constraint)
  - Proper phase encoding for each (n, l, m_l, m_s)
"""

import numpy as np
import os

print("=" * 70)
print("EXP_043j: Simplex Network IE — Complex C⁵")
print("=" * 70)

alpha_GUT = 6.0 / (25 * np.pi**2)  # ≈ 0.0243
sqrt_aGUT = np.sqrt(alpha_GUT)      # ≈ 0.156
IE_H = 13.598  # eV


# ═══════════════════════════════════════════════════════════════
#  C⁵ vector construction
# ═══════════════════════════════════════════════════════════════

def psi_S(direction):
    """S vertex: pure C³, direction 0/1/2."""
    v = np.zeros(5, dtype=complex)
    v[2 + direction] = 1.0
    return v

def psi_electron(n, l, m_l, m_s):
    """Electron T vertex ∈ C⁵.

    C³ amplitude = √α_GUT / n  (coupling to nucleus)
    C³ direction: l, m_l
      l=0: (1,1,1)/√3 isotropic
      l=1: m_l selects axis
      l=2: pair of axes
      l=3: all three (with phase)

    C² amplitude = √(1 - c3²)
    C² direction: unique per (n, l, m_l, m_s) via phase encoding
      θ_C2 = π(n-1)/7 + πm_l/(4l+2) + πl/6
      spin: m_s>0 → (cos,sin), m_s<0 → (-sin,cos) [orthogonal]
    """
    v = np.zeros(5, dtype=complex)

    c3_amp = sqrt_aGUT / n

    # C³ direction with COMPLEX phases for uniqueness
    golden = (1 + np.sqrt(5)) / 2
    base_phase = 2 * np.pi * (n + l * golden + m_l * golden**2) / 7

    if l == 0:
        v[2] = c3_amp / np.sqrt(3) * np.exp(1j * base_phase)
        v[3] = c3_amp / np.sqrt(3) * np.exp(1j * (base_phase + 2*np.pi/3))
        v[4] = c3_amp / np.sqrt(3) * np.exp(1j * (base_phase + 4*np.pi/3))
    elif l == 1:
        idx = (m_l + 1) % 3  # m_l=-1→0, m_l=0→1, m_l=1→2
        v[2 + idx] = c3_amp * np.exp(1j * base_phase)
    elif l == 2:
        r = 1.0 / np.sqrt(2)
        idx1 = (m_l + 2) % 3
        idx2 = (m_l + 3) % 3
        v[2 + idx1] = c3_amp * r * np.exp(1j * base_phase)
        v[2 + idx2] = c3_amp * r * np.exp(1j * (base_phase + np.pi * m_l / 5))
    else:  # l >= 3
        v[2] = c3_amp / np.sqrt(3) * np.exp(1j * base_phase)
        v[3] = c3_amp / np.sqrt(3) * np.exp(1j * (base_phase + np.pi/3))
        v[4] = c3_amp / np.sqrt(3) * np.exp(1j * (base_phase + 2*np.pi/3))

    # C² part
    c2_amp = np.sqrt(max(1.0 - c3_amp**2, 0.01))
    theta_c2 = np.pi * (n - 1) / 7 + np.pi * m_l / max(4*l + 2, 2) + np.pi * l / 6

    if m_s > 0:
        v[0] = c2_amp * np.cos(theta_c2) * np.exp(1j * base_phase * 0.1)
        v[1] = c2_amp * np.sin(theta_c2) * np.exp(1j * base_phase * 0.2)
    else:
        v[0] = -c2_amp * np.sin(theta_c2) * np.exp(1j * base_phase * 0.3)
        v[1] = c2_amp * np.cos(theta_c2) * np.exp(1j * base_phase * 0.4)

    # Normalize
    v /= np.linalg.norm(v)
    return v

def psi_slot(n, l, m_l, m_s):
    """Slot T vertex — orthogonal to electron in C² subspace."""
    v = psi_electron(n, l, m_l, -m_s)  # opposite spin = nearly orthogonal
    # Add small perturbation for uniqueness
    phase = np.pi * (n * 7 + l * 13 + m_l * 17 + (1 if m_s > 0 else 0) * 23)
    v *= np.exp(1j * phase * 0.01)
    v /= np.linalg.norm(v)
    return v


# ═══════════════════════════════════════════════════════════════
#  Atom builder
# ═══════════════════════════════════════════════════════════════

def madelung_subshells():
    subs = []
    for n in range(1, 9):
        for l in range(n):
            subs.append((n, l))
    subs.sort(key=lambda x: (x[0] + x[1], x[0]))
    return subs

def electron_config_full(Z):
    """Full quantum number list: [(n, l, m_l, m_s), ...]"""
    subs = madelung_subshells()
    elecs = []
    remaining = Z
    for n, l in subs:
        if remaining <= 0:
            break
        cap = 2 * (2*l + 1)
        # Hund: fill all m_l spin-up, then spin-down
        for ms in [+0.5, -0.5]:
            for ml in range(-l, l+1):
                if remaining <= 0:
                    break
                elecs.append((n, l, ml, ms))
                remaining -= 1
    return elecs


def build_atom_network(Z):
    """Build full simplex network for atom Z.

    Returns: list of all ψ vectors, mapping info
    Vertices: S₁, S₂, S₃, then for each electron: T_e, T_slot
    Total: 3 + 2Z vertices
    """
    elecs = electron_config_full(Z)

    psi_list = []
    labels = []

    # S vertices (nucleus)
    for d in range(3):
        psi_list.append(psi_S(d))
        labels.append(f'S{d+1}')

    # T vertices (electron + slot pairs)
    for i, (n, l, ml, ms) in enumerate(elecs):
        orb = f"{n}{'spdf'[min(l,3)]}"
        psi_list.append(psi_electron(n, l, ml, ms))
        labels.append(f'e{i+1}({orb})')
        psi_list.append(psi_slot(n, l, ml, ms))
        labels.append(f's{i+1}({orb})')

    return psi_list, labels, elecs


def gram_matrix(psi_list):
    """Complex Gram matrix G_ij = ⟨ψ_i|ψ_j⟩."""
    Psi = np.array(psi_list)  # N × 5
    return Psi @ Psi.conj().T  # N × N, Hermitian PSD


# ═══════════════════════════════════════════════════════════════
#  IE calculation
# ═══════════════════════════════════════════════════════════════

def compute_IE(Z):
    """IE = log|det(G_full)| - log|det(G_ionized)|.

    Remove outermost electron + its slot (last 2 rows/cols).
    """
    if Z == 0:
        return 0, {}

    psi_list, labels, elecs = build_atom_network(Z)
    G = gram_matrix(psi_list)

    # Regularize
    G += 1e-14 * np.eye(G.shape[0])

    sign_f, logdet_f = np.linalg.slogdet(G)

    # Remove last electron + slot (last 2 vertices)
    G_ion = G[:-2, :-2]
    sign_i, logdet_i = np.linalg.slogdet(G_ion)

    delta = logdet_f - logdet_i

    outer = elecs[-1]
    return delta, {
        'n': outer[0], 'l': outer[1], 'm_l': outer[2], 'm_s': outer[3],
        'orbital': f"{outer[0]}{'spdf'[min(outer[1],3)]}",
        'logdet_full': logdet_f,
        'logdet_ion': logdet_i,
        'matrix_size': G.shape[0],
    }


# ═══════════════════════════════════════════════════════════════
#  NIST data
# ═══════════════════════════════════════════════════════════════

NIST_IE = {
    1:13.598, 2:24.587, 3:5.392, 4:9.323, 5:8.298, 6:11.260, 7:14.534,
    8:13.618, 9:17.423, 10:21.565, 11:5.139, 12:7.646, 13:5.986,
    14:8.152, 15:10.487, 16:10.360, 17:12.968, 18:15.760, 19:4.341,
    20:6.113, 21:6.561, 22:6.828, 23:6.746, 24:6.767, 25:7.434,
    26:7.902, 27:7.881, 28:7.640, 29:7.726, 30:9.394, 31:5.999,
    32:7.899, 33:9.789, 34:9.752, 35:11.814, 36:14.000,
}

ELEM = {}
names = ('H He Li Be B C N O F Ne Na Mg Al Si P S Cl Ar K Ca '
         'Sc Ti V Cr Mn Fe Co Ni Cu Zn Ga Ge As Se Br Kr').split()
for i, name in enumerate(names):
    ELEM[i+1] = name


# ═══════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":

    print(f"\nComputing Δ(log det) for Z=1 to 36...")
    print(f"{'Z':>3s} {'Sym':>3s} {'orb':>4s} {'size':>5s} {'Δlogdet':>10s}")
    print("─" * 35)

    deltas = {}
    infos = {}
    for Z in range(1, 37):
        d, info = compute_IE(Z)
        deltas[Z] = d
        infos[Z] = info
        sym = ELEM.get(Z, '')
        sz = info.get('matrix_size', 0)
        print(f"{Z:>3d} {sym:>3s} {info.get('orbital','?'):>4s} {sz:>5d} {d:>10.5f}")

    # Fit scale: IE = scale × |Δlogdet|
    Zs = [Z for Z in range(1, 37) if abs(deltas[Z]) > 1e-10]
    d_vals = np.array([abs(deltas[Z]) for Z in Zs])
    ie_vals = np.array([NIST_IE[Z] for Z in Zs])
    scale = np.sum(d_vals * ie_vals) / np.sum(d_vals**2)

    print(f"\n  Scale = {scale:.4f} eV per unit |Δlogdet|")

    # Full results
    print(f"\n{'═' * 70}")
    print(f"IE Results: IE = {scale:.2f} × |Δlogdet|")
    print(f"{'═' * 70}")
    print(f"\n{'Z':>3s} {'Sym':>3s} {'orb':>4s} {'Δlogdet':>10s} "
          f"{'DRLT IE':>8s} {'NIST IE':>8s} {'err%':>7s}")
    print("─" * 55)

    errors = []
    for Z in range(1, 37):
        d = deltas[Z]
        ie_drlt = scale * abs(d)
        ie_nist = NIST_IE[Z]
        err = (ie_drlt - ie_nist) / ie_nist * 100
        errors.append(abs(err))
        sym = ELEM.get(Z, '')
        orb = infos[Z].get('orbital', '?')
        flag = '✓' if abs(err) < 20 else ''
        print(f"{Z:>3d} {sym:>3s} {orb:>4s} {d:>10.5f} "
              f"{ie_drlt:>8.2f} {ie_nist:>8.3f} {err:>+7.1f}% {flag}")

    print(f"\n  평균 |오차|: {np.mean(errors):.1f}%")
    print(f"  중앙값: {np.median(errors):.1f}%")
    print(f"  10% 이내: {sum(1 for e in errors if e < 10)}/{len(errors)}")
    print(f"  20% 이내: {sum(1 for e in errors if e < 20)}/{len(errors)}")
    print(f"  30% 이내: {sum(1 for e in errors if e < 30)}/{len(errors)}")
    print(f"  50% 이내: {sum(1 for e in errors if e < 50)}/{len(errors)}")

    # Noble gas peaks
    print(f"\n  Noble gas IE peaks:")
    for nz in [2, 10, 18, 36]:
        d_noble = scale * abs(deltas[nz])
        d_prev = scale * abs(deltas.get(nz-1, 0))
        d_next = scale * abs(deltas.get(nz+1, 0)) if nz < 36 else 0
        peak = d_noble > d_prev and (nz >= 36 or d_noble > d_next)
        sym = ELEM[nz]
        print(f"    {sym} (Z={nz}): IE_DRLT={d_noble:.2f}, "
              f"prev={d_prev:.2f}, next={d_next:.2f} "
              f"{'PEAK ✓' if peak else 'no peak'}")

    # Subshell structure check
    print(f"\n  Subshell IE trends:")
    prev_orb = ""
    for Z in range(1, 37):
        orb = infos[Z].get('orbital', '?')
        if orb != prev_orb:
            print(f"    --- {orb} ---")
            prev_orb = orb
        ie_drlt = scale * abs(deltas[Z])
        sym = ELEM.get(Z, '')
        print(f"      {sym:>3s} (Z={Z}): {ie_drlt:.2f} eV (NIST: {NIST_IE[Z]:.2f})")

    # Save
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_043j_Simplex_Network_IE.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_043j: Simplex Network IE — Full C⁵ Complex Vectors\n")
        f.write(f"Scale = {scale:.4f} eV\n")
        f.write(f"Mean |error|: {np.mean(errors):.1f}%\n")
        f.write(f"Median: {np.median(errors):.1f}%\n")
        f.write(f"Within 20%: {sum(1 for e in errors if e<20)}/{len(errors)}\n")
        f.write(f"Within 30%: {sum(1 for e in errors if e<30)}/{len(errors)}\n\n")
        for Z in range(1, 37):
            ie_drlt = scale * abs(deltas[Z])
            err = (ie_drlt - NIST_IE[Z]) / NIST_IE[Z] * 100
            sym = ELEM.get(Z, '')
            orb = infos[Z].get('orbital', '?')
            f.write(f"Z={Z:>2d} {sym:>3s} {orb:>3s} "
                    f"DRLT={ie_drlt:>7.2f} NIST={NIST_IE[Z]:>7.3f} "
                    f"err={err:>+6.1f}%\n")
    print(f"\n결과 저장: {outfile}")
