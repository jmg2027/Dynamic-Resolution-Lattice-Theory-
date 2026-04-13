"""
EXP_044: Simplex Atoms — Unnormalized ψ, cross-hinges, correct IE
===================================================================

Key change from EXP_043: ψ vectors are NOT normalized.
  |ψ_T|² = α_GUT / n²  (coupling strength, not 1)
  |ψ_S|² = 1            (nucleus fully present)

This makes the Gram matrix have structure:
  G_SS ≈ I₃  (dominant)
  G_TT diag ≈ α_GUT/n²  (small, shell-dependent)
  G_ST ≈ α_GUT/(n√3)    (coupling)

IE = Δ(log det) when removing outermost electron.
"""

import numpy as np
import os

alpha_GUT = 6.0 / (25 * np.pi**2)
sqrt_aGUT = np.sqrt(alpha_GUT)
IE_H = 13.598

print("=" * 70)
print("EXP_044: Simplex Atoms — Unnormalized ψ")
print(f"  α_GUT = {alpha_GUT:.6f}, √α_GUT = {sqrt_aGUT:.4f}")
print("=" * 70)


# ═══════════════════════════════════════════════════════════════
#  ψ construction (UNNORMALIZED)
# ═══════════════════════════════════════════════════════════════

def psi_S(d):
    """S vertex: unit vector in C³ direction d."""
    v = np.zeros(5, dtype=complex)
    v[2 + d] = 1.0
    return v

def psi_T(n, l, m_l, m_s):
    """T vertex: amplitude = √α_GUT / n.

    |ψ|² = α_GUT / n² (NOT 1).
    Direction in C⁵ from quantum numbers.
    """
    # Unit direction in C⁵
    direction = np.zeros(5, dtype=complex)

    # C² part
    golden = (1 + np.sqrt(5)) / 2
    theta = np.pi * (n - 1 + (m_l + l) / max(2*l+1, 1)) / 4
    phase = 2 * np.pi * (n * golden + l * golden**2 + m_l) / 7

    if m_s > 0:
        direction[0] = np.cos(theta) * np.exp(1j * phase)
        direction[1] = np.sin(theta) * np.exp(1j * phase * 1.3)
    else:
        direction[0] = -np.sin(theta) * np.exp(1j * phase * 0.7)
        direction[1] = np.cos(theta) * np.exp(1j * phase * 1.1)

    # C³ part: l determines direction
    c3_frac = 0.3  # fraction of direction in C³ (constant)
    c2_frac = np.sqrt(1 - c3_frac**2)

    if l == 0:
        direction[2] += c3_frac / np.sqrt(3) * np.exp(1j * phase)
        direction[3] += c3_frac / np.sqrt(3) * np.exp(1j * (phase + 2*np.pi/3))
        direction[4] += c3_frac / np.sqrt(3) * np.exp(1j * (phase + 4*np.pi/3))
    elif l == 1:
        idx = (m_l + 1) % 3
        direction[2 + idx] += c3_frac * np.exp(1j * phase)
    elif l == 2:
        idx1 = (m_l + 2) % 3
        idx2 = (m_l + 3) % 3
        direction[2 + idx1] += c3_frac / np.sqrt(2) * np.exp(1j * phase)
        direction[2 + idx2] += c3_frac / np.sqrt(2) * np.exp(1j * (phase + np.pi*m_l/5))
    else:
        direction[2] += c3_frac / np.sqrt(3) * np.exp(1j * phase)
        direction[3] += c3_frac / np.sqrt(3) * np.exp(1j * (phase + np.pi/3))
        direction[4] += c3_frac / np.sqrt(3) * np.exp(1j * (phase + 2*np.pi/3))

    # Scale C² part
    direction[0] *= c2_frac
    direction[1] *= c2_frac

    # Normalize direction, then scale by coupling
    norm = np.linalg.norm(direction)
    if norm > 1e-15:
        direction /= norm

    # UNNORMALIZED: amplitude = √α_GUT / n
    return (sqrt_aGUT / n) * direction


def psi_slot(n, l, m_l, m_s):
    """Slot: same amplitude, orthogonal direction."""
    return psi_T(n, l, m_l, -m_s) * np.exp(1j * 0.5)


# ═══════════════════════════════════════════════════════════════
#  Atom builder
# ═══════════════════════════════════════════════════════════════

def madelung():
    subs = []
    for n in range(1, 9):
        for l in range(n):
            subs.append((n, l))
    subs.sort(key=lambda x: (x[0]+x[1], x[0]))
    return subs

def electron_config(Z):
    subs = madelung()
    elecs = []
    remaining = Z
    for n, l in subs:
        if remaining <= 0:
            break
        for ms in [+0.5, -0.5]:
            for ml in range(-l, l+1):
                if remaining <= 0:
                    break
                elecs.append((n, l, ml, ms))
                remaining -= 1
    return elecs

def build_atom(Z):
    """Build atom: 3 S + 2Z T vertices, unnormalized."""
    elecs = electron_config(Z)
    psi_list = []
    labels = []

    for d in range(3):
        psi_list.append(psi_S(d))
        labels.append(f'S{d+1}')

    for i, (n, l, ml, ms) in enumerate(elecs):
        psi_list.append(psi_T(n, l, ml, ms))
        labels.append(f'e{i+1}({n}{"spdf"[l]})')
        psi_list.append(psi_slot(n, l, ml, ms))
        labels.append(f's{i+1}')

    return psi_list, labels, elecs


# ═══════════════════════════════════════════════════════════════
#  IE
# ═══════════════════════════════════════════════════════════════

def compute_IE(Z):
    if Z == 0:
        return 0, {}

    psi_list, labels, elecs = build_atom(Z)
    Psi = np.array(psi_list)
    G = Psi @ Psi.conj().T
    G += 1e-14 * np.eye(G.shape[0])

    _, logdet_f = np.linalg.slogdet(G)

    G_ion = G[:-2, :-2]
    _, logdet_i = np.linalg.slogdet(G_ion)

    delta = logdet_f - logdet_i

    outer = elecs[-1]
    # Also compute G eigenvalues
    eigvals = np.sort(np.abs(np.linalg.eigvalsh(G)))[::-1]

    return delta, {
        'n': outer[0], 'l': outer[1],
        'orbital': f"{outer[0]}{'spdf'[outer[1]]}",
        'logdet_f': logdet_f,
        'logdet_i': logdet_i,
        'top5_eig': eigvals[:5],
        'psi_norm_sq': float(np.real(np.vdot(psi_list[-2], psi_list[-2]))),
    }


# ═══════════════════════════════════════════════════════════════
#  NIST + Run
# ═══════════════════════════════════════════════════════════════

NIST_IE = {
    1:13.598, 2:24.587, 3:5.392, 4:9.323, 5:8.298, 6:11.260, 7:14.534,
    8:13.618, 9:17.423, 10:21.565, 11:5.139, 12:7.646, 13:5.986,
    14:8.152, 15:10.487, 16:10.360, 17:12.968, 18:15.760, 19:4.341,
    20:6.113, 21:6.561, 22:6.828, 23:6.746, 24:6.767, 25:7.434,
    26:7.902, 27:7.881, 28:7.640, 29:7.726, 30:9.394, 31:5.999,
    32:7.899, 33:9.789, 34:9.752, 35:11.814, 36:14.000,
}
ELEM = dict(enumerate('_ H He Li Be B C N O F Ne Na Mg Al Si P S Cl Ar K Ca Sc Ti V Cr Mn Fe Co Ni Cu Zn Ga Ge As Se Br Kr'.split()))

if __name__ == "__main__":

    # First: show H in detail
    print("\n─── Hydrogen detail ───")
    psi_list, labels, elecs = build_atom(1)
    print(f"  Vertices: {len(psi_list)}")
    for i, (psi, lbl) in enumerate(zip(psi_list, labels)):
        norm_sq = float(np.real(np.vdot(psi, psi)))
        print(f"  {lbl:>8s}: |ψ|² = {norm_sq:.6f}")

    Psi = np.array(psi_list)
    G = Psi @ Psi.conj().T
    print(f"\n  G matrix ({G.shape[0]}×{G.shape[0]}):")
    print(f"  |G| =")
    for i in range(G.shape[0]):
        row = "    "
        for j in range(G.shape[1]):
            row += f"{abs(G[i,j]):8.5f}"
        print(row)

    # All elements
    print(f"\n{'═' * 70}")
    print(f"{'Z':>3s} {'Sym':>3s} {'orb':>3s} {'|ψ|²':>8s} {'Δlogdet':>10s} "
          f"{'DRLT':>8s} {'NIST':>8s} {'err%':>7s}")
    print("─" * 60)

    deltas = {}
    infos = {}
    for Z in range(1, 37):
        d, info = compute_IE(Z)
        deltas[Z] = d
        infos[Z] = info

    # Scale
    Zs = [Z for Z in range(1,37) if abs(deltas[Z]) > 1e-15]
    d_vals = np.array([abs(deltas[Z]) for Z in Zs])
    ie_vals = np.array([NIST_IE[Z] for Z in Zs])
    scale = np.sum(d_vals * ie_vals) / np.sum(d_vals**2)

    errors = []
    for Z in range(1, 37):
        d = deltas[Z]
        info = infos[Z]
        ie_d = scale * abs(d)
        ie_n = NIST_IE[Z]
        err = (ie_d - ie_n) / ie_n * 100
        errors.append(abs(err))
        sym = ELEM.get(Z, '')
        flag = '✓' if abs(err) < 20 else ''
        print(f"{Z:>3d} {sym:>3s} {info['orbital']:>3s} {info['psi_norm_sq']:>8.5f} "
              f"{d:>10.5f} {ie_d:>8.2f} {ie_n:>8.3f} {err:>+7.1f}% {flag}")

    print(f"\n  Scale = {scale:.4f}")
    print(f"  평균 |오차|: {np.mean(errors):.1f}%")
    print(f"  중앙값: {np.median(errors):.1f}%")
    print(f"  10% 이내: {sum(1 for e in errors if e<10)}/{len(errors)}")
    print(f"  20% 이내: {sum(1 for e in errors if e<20)}/{len(errors)}")
    print(f"  30% 이내: {sum(1 for e in errors if e<30)}/{len(errors)}")

    # Save
    results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
    outfile = os.path.join(results_dir, "EXP_044_Simplex_Atoms.txt")
    with open(outfile, 'w') as f:
        f.write("EXP_044: Simplex Atoms — Unnormalized ψ\n")
        f.write(f"Scale = {scale:.4f}\n")
        f.write(f"Mean |error|: {np.mean(errors):.1f}%\n")
        f.write(f"Within 20%: {sum(1 for e in errors if e<20)}/{len(errors)}\n\n")
        for Z in range(1, 37):
            ie_d = scale * abs(deltas[Z])
            err = (ie_d-NIST_IE[Z])/NIST_IE[Z]*100
            f.write(f"Z={Z:>2d} {ELEM.get(Z,''):>3s} IE={ie_d:>7.2f} NIST={NIST_IE[Z]:>7.3f} err={err:>+6.1f}%\n")
    print(f"\n결과 저장: {outfile}")
