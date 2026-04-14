"""
EXP_045: Hydrogen Simplex — Exact Complex Values
=================================================

Simplex = 5 vertices, each a single complex number.
Hydrogen: (u₁, u₂, d, e⁻, slot)

What values? Let's figure out from physics:
- Quarks form equilateral triangle in C (max SSS area = confinement)
- Electron is small and far in phase (weak EM coupling)
- Slot is ~0 (empty)

Edges: z_i* z_j = boson channel
Hinges: triangle area in complex plane = force strength
"""

import numpy as np
from itertools import combinations

print("=" * 65)
print("EXP_045: Hydrogen Simplex — Complex Values")
print("=" * 65)

alpha_em = 1/137.036
alpha_GUT = 6/(25*np.pi**2)
sqrt_alpha = np.sqrt(alpha_em)


# ═══════════════════════════════════════════════════════════════
#  Triangle area in complex plane
# ═══════════════════════════════════════════════════════════════

def triangle_area(z1, z2, z3):
    """Area of triangle formed by 3 complex numbers."""
    return 0.5 * abs(np.imag((z2 - z1) * np.conj(z3 - z1)))

def edge_weight(z1, z2):
    """Edge = z₁* z₂ (boson channel)."""
    return np.conj(z1) * z2


# ═══════════════════════════════════════════════════════════════
#  Hydrogen: assign values
# ═══════════════════════════════════════════════════════════════

# Quarks: equilateral triangle on unit circle
# u₁ = 1, u₂ = ω, d = ω² where ω = e^{2πi/3}
omega = np.exp(2j * np.pi / 3)

# Electron: small amplitude, different phase sector
# |e| ~ sqrt(α_em) gives the coupling strength
# Phase: π (opposite side of complex plane from quarks)

# Slot: essentially 0 (empty state)

configs = {
    "A: quarks=unit circle, e=√α_em": {
        'u1': 1.0,
        'u2': omega,
        'd':  omega**2,
        'e':  sqrt_alpha * np.exp(1j * np.pi),
        'slot': 1e-6,
    },
    "B: quarks=unit, e=α_em": {
        'u1': 1.0,
        'u2': omega,
        'd':  omega**2,
        'e':  alpha_em * np.exp(1j * np.pi),
        'slot': 1e-6,
    },
    "C: quarks=unit, e=√α_GUT": {
        'u1': 1.0,
        'u2': omega,
        'd':  omega**2,
        'e':  np.sqrt(alpha_GUT) * np.exp(1j * np.pi),
        'slot': 1e-6,
    },
    "D: quarks=unit, e=α_GUT": {
        'u1': 1.0,
        'u2': omega,
        'd':  omega**2,
        'e':  alpha_GUT * np.exp(1j * np.pi),
        'slot': 1e-6,
    },
}

vertex_names = ['u1', 'u2', 'd', 'e', 'slot']
vertex_types = {'u1': 'S', 'u2': 'S', 'd': 'S', 'e': 'T', 'slot': 'T'}

for config_name, verts in configs.items():
    print(f"\n{'─' * 65}")
    print(f"  Config {config_name}")
    print(f"{'─' * 65}")

    vals = [verts[n] for n in vertex_names]

    # Print vertex values
    print(f"\n  Vertices:")
    for name in vertex_names:
        z = verts[name]
        print(f"    {name:>5s} = {z:.6f}  (|z| = {abs(z):.6f}, arg = {np.degrees(np.angle(z)):+.1f}°)")

    # C⁵ vector
    psi = np.array(vals)
    norm_sq = np.vdot(psi, psi)
    print(f"\n  ψ = ({', '.join(f'{z:.4f}' for z in vals)})")
    print(f"  |ψ|² = {np.real(norm_sq):.6f}")

    # ── All 10 edges (boson channels) ──
    print(f"\n  Edges (boson channels: z_i* z_j):")
    for i, j in combinations(range(5), 2):
        ni, nj = vertex_names[i], vertex_names[j]
        ti, tj = vertex_types[ni], vertex_types[nj]
        e = edge_weight(vals[i], vals[j])
        etype = f"{ti}{tj}"
        print(f"    {ni:>5s}-{nj:<5s} ({etype}): "
              f"G = {e:.6f}, |G| = {abs(e):.6f}, W = {abs(e)**2/5:.6f}")

    # ── All 10 hinges (triangle areas) ──
    print(f"\n  Hinges (triangle area in complex plane):")

    hinge_data = {'SSS': [], 'SST': [], 'STT': [], 'TTT': []}
    for tri in combinations(range(5), 3):
        names = [vertex_names[k] for k in tri]
        types = [vertex_types[n] for n in names]
        n_s = types.count('S')
        htype = {3:'SSS', 2:'SST', 1:'STT', 0:'TTT'}[n_s]

        z1, z2, z3 = [vals[k] for k in tri]
        area = triangle_area(z1, z2, z3)
        hinge_data[htype].append(area)

        print(f"    ({','.join(names):>12s}) [{htype}]: A = {area:.8f}")

    # ── Summary ──
    print(f"\n  Summary:")
    for ht in ['SSS', 'SST', 'STT']:
        if hinge_data[ht]:
            areas = hinge_data[ht]
            print(f"    {ht}: {len(areas)} hinges, "
                  f"⟨A⟩ = {np.mean(areas):.8f}, "
                  f"total = {sum(areas):.8f}")

    # Ratios
    a_sss = np.mean(hinge_data['SSS']) if hinge_data['SSS'] else 0
    a_sst = np.mean(hinge_data['SST']) if hinge_data['SST'] else 0
    a_stt = np.mean(hinge_data['STT']) if hinge_data['STT'] else 0

    if a_sss > 0:
        print(f"\n    SST/SSS = {a_sst/a_sss:.6f}")
        if a_stt > 0:
            print(f"    STT/SSS = {a_stt/a_sss:.6f}")
        print(f"    SST/SSS ≈ α_em? {a_sst/a_sss:.6f} vs {alpha_em:.6f}")
        print(f"    SST/SSS ≈ √α_em? {a_sst/a_sss:.6f} vs {sqrt_alpha:.6f}")
        print(f"    SST/SSS ≈ α_GUT? {a_sst/a_sss:.6f} vs {alpha_GUT:.6f}")

    # What physical quantities can we extract?
    print(f"\n  Physical interpretation:")
    print(f"    SSS area = proton binding ∝ Λ_QCD")
    print(f"    SST area = EM coupling ∝ α_em")
    print(f"    STT area = weak/kinetic ∝ α_weak")

    # ħ = A / (4 ln 2)
    if a_sss > 0:
        hbar_sss = a_sss / (4 * np.log(2))
        hbar_sst = a_sst / (4 * np.log(2))
        print(f"    ħ(SSS) = {hbar_sss:.8f}")
        print(f"    ħ(SST) = {hbar_sst:.8f}")


# ═══════════════════════════════════════════════════════════════
#  Which config gives α_em correctly?
# ═══════════════════════════════════════════════════════════════

print(f"\n{'═' * 65}")
print(f"Which |e| gives SST/SSS = α_em = {alpha_em:.6f}?")
print(f"{'═' * 65}")

# Scan |e| to match α_em ratio
for e_amp_100 in range(1, 50):
    e_amp = e_amp_100 / 1000.0
    v = [1.0, omega, omega**2, e_amp * np.exp(1j*np.pi), 1e-6]

    a_sss = triangle_area(v[0], v[1], v[2])
    # Average SST
    sst_areas = []
    for tri in combinations(range(5), 3):
        types = [vertex_types[vertex_names[k]] for k in tri]
        if types.count('S') == 2 and types.count('T') == 1:
            sst_areas.append(triangle_area(v[tri[0]], v[tri[1]], v[tri[2]]))
    a_sst = np.mean(sst_areas) if sst_areas else 0

    ratio = a_sst / a_sss if a_sss > 0 else 0
    if abs(ratio - alpha_em) / alpha_em < 0.1:
        print(f"  |e| = {e_amp:.4f}: SST/SSS = {ratio:.6f} (target: {alpha_em:.6f}, err: {(ratio-alpha_em)/alpha_em*100:+.1f}%)")

# Save
import os
results_dir = os.path.join(os.path.dirname(__file__), "..", "results")
outfile = os.path.join(results_dir, "EXP_045_Hydrogen_Simplex.txt")
with open(outfile, 'w') as f:
    f.write("EXP_045: Hydrogen Simplex — Exact Complex Values\n")
    f.write("See terminal output for full results.\n")
print(f"\n결과 저장: {outfile}")
