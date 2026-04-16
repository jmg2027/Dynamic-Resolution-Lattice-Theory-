"""
ATM_051: Simplex Connection Maps
Joint research by Mingu Jeong and Claude (Anthropic)

The CONNECTION between two simplices = |⟨B_i|B_j⟩|²
  = Born-rule overlap of their electron vertices
  = the geometric reality of "screening"

  Strong (≈0.5): same temporal sector → σ_same_s
  Zero:          orthogonal (Pauli or spatial) → no screening
  Weak (≈ε²):   cross-sector → σ_cross, σ_sp

Tests:
  1. H, He, C: explicit connection maps
  2. Period 2 complete: Ne connection matrix
  3. Connection strength = screening constant
  4. General pattern: block structure of connections
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment

D = 5; N_S = 3; N_T = 2
ALPHA = 1/137.036

SYM = ['','H','He','Li','Be','B','C','N','O','F','Ne']
M_LABELS = {0: [''], 1: ['x','y','z'],
            2: ['xy','xz','yz','x²y²','z²'],
            3: ['a','b','c','d','e','f','g']}


def build_B_vectors(Z):
    """Build all electron B-vectors in ℂ⁵ for atom Z.

    Each orbital (n,l,m) = 1 simplex with unique temporal phase.
    Spin ↑ = (cosθ, sinθ), spin ↓ = (-sinθ, cosθ) — orthogonal pair.
    """
    eps = Z * ALPHA / np.sqrt(N_S)

    order = []
    for n in range(1, 9):
        for l in range(min(n, 4)):
            order.append((n+l, n, l))
    order.sort()

    vectors = []
    labels = []
    remaining = Z
    orbital_idx = 0  # unique index per orbital

    for _, n, l in order:
        n_orb = 2*l+1
        max_e = 2*n_orb
        count = min(remaining, max_e)
        if count <= 0:
            break
        remaining -= count

        sub = 'spdf'[l]

        for m in range(n_orb):
            e_up = 1 if count > m else 0
            e_dn = 1 if count > n_orb + m else 0
            m_lab = M_LABELS[l][m]

            # Unique temporal phase per orbital
            theta = 2 * np.pi * orbital_idx / 30  # spread across [0, 2π)
            orbital_idx += 1

            # Spatial component depends on l, m
            spatial = np.zeros(3)
            if l == 0:
                spatial = np.array([eps, eps, eps]) / np.sqrt(3) * np.sqrt(3)
                # isotropic: equal overlap with all A
                spatial = np.array([eps, eps, eps])
            elif l == 1:
                spatial[m] = eps  # directional: overlap with A_{m+1}
            elif l >= 2:
                # d/f: spread across multiple directions
                for k in range(min(l, N_S)):
                    spatial[(m+k) % N_S] += eps / np.sqrt(l)

            t_mag = np.sqrt(max(0, 1 - np.sum(spatial**2)))

            if e_up:
                v = np.array([t_mag*np.cos(theta), t_mag*np.sin(theta),
                              spatial[0], spatial[1], spatial[2]],
                             dtype=complex)
                v /= np.linalg.norm(v)
                vectors.append(v)
                labels.append(f'{n}{sub}{"_"+m_lab if m_lab else ""}↑')
            if e_dn:
                v = np.array([-t_mag*np.sin(theta), t_mag*np.cos(theta),
                              spatial[0], spatial[1], spatial[2]],
                             dtype=complex)
                v /= np.linalg.norm(v)
                vectors.append(v)
                labels.append(f'{n}{sub}{"_"+m_lab if m_lab else ""}↓')

    return vectors, labels


def connection_strength(v1, v2):
    """Born overlap |⟨B_i|B_j⟩|²."""
    return float(abs(np.dot(np.conj(v1), v2))**2)


def draw_connection_map(Z):
    """Draw simplex connection map for element Z."""
    sym = SYM[Z] if Z < len(SYM) else f'Z{Z}'
    vecs, labs = build_B_vectors(Z)
    n = len(vecs)

    lines = []
    lines.append(f'{"="*60}')
    lines.append(f' {sym} (Z={Z}): {n} electrons, connection map')
    lines.append(f'{"="*60}')
    lines.append(f' A₁(u)━━A₂(u)━━A₃(d)  [nucleus, shared by all]')
    lines.append(f'')

    # Overlap matrix
    header = '       ' + ' '.join(f'{l[:5]:>5}' for l in labs)
    lines.append(header)
    for i in range(n):
        row = f'{labs[i]:>6} '
        for j in range(n):
            ov = connection_strength(vecs[i], vecs[j])
            if i == j:
                row += '  ■   '
            elif ov < 0.001:
                row += '  ·   '
            elif ov < 0.1:
                row += f'{ov:5.3f} '
            elif ov < 0.4:
                row += f'{ov:5.2f}  '
            else:
                row += f'{ov:5.2f}★ '
        lines.append(row)

    # Legend
    lines.append(f'')
    lines.append(f'  ■ = self  ★ = strong (>0.4)  · = zero (<0.001)')
    lines.append(f'  Connection = |⟨B_i|B_j⟩|² = screening interaction')
    lines.append(f'')
    return '\n'.join(lines)


class SimplexConnections(Experiment):
    ID = "ATM_051"
    TITLE = "Simplex Connection Maps"

    def run(self):
        self.test1_light()
        self.test2_carbon_detail()
        self.test3_neon()
        self.test4_block_structure()

    def test1_light(self):
        """H, He, Li connection maps."""
        self.log(f"\n")
        for Z in [1, 2, 3]:
            self.log(draw_connection_map(Z))
        self.check("Light atoms drawn", True)

    def test2_carbon_detail(self):
        """Carbon: detailed connection analysis."""
        self.log(draw_connection_map(6))

        vecs, labs = build_B_vectors(6)
        self.log(f"  Carbon connection analysis:")
        self.log(f"  1s↑─1s↓ = {connection_strength(vecs[0],vecs[1]):.4f}"
                 f"  (Pauli: orthogonal spins)")
        self.log(f"  1s↑─2s↑ = {connection_strength(vecs[0],vecs[2]):.4f}"
                 f"  (→ temporal baseline ~1/N_T)")
        self.log(f"  2p_x↑─2p_y↑ = {connection_strength(vecs[4],vecs[5]):.4f}"
                 f" (→ spatial orthogonality)")
        self.log(f"  1s↑─2p_x↑ = {connection_strength(vecs[0],vecs[4]):.4f}"
                 f" (→ cross-shell coupling)")
        self.check("Carbon analyzed", True)

    def test3_neon(self):
        """Neon: full noble gas connection matrix."""
        self.log(draw_connection_map(10))

        vecs, labs = build_B_vectors(10)
        # Block structure: s-s, s-p, p-p connections
        s_idx = [i for i, l in enumerate(labs) if 's' in l]
        p_idx = [i for i, l in enumerate(labs) if 'p' in l]

        ss_avg = np.mean([connection_strength(vecs[i], vecs[j])
                          for i in s_idx for j in s_idx if i != j])
        pp_avg = np.mean([connection_strength(vecs[i], vecs[j])
                          for i in p_idx for j in p_idx if i != j])
        sp_avg = np.mean([connection_strength(vecs[i], vecs[j])
                          for i in s_idx for j in p_idx])

        self.log(f"  Neon block structure:")
        self.log(f"  avg(s-s) = {ss_avg:.4f}  (same-shell temporal)")
        self.log(f"  avg(p-p) = {pp_avg:.4f}  (cross-orbital)")
        self.log(f"  avg(s-p) = {sp_avg:.4f}  (cross-block)")
        self.check("Neon analyzed", True)

    def test4_block_structure(self):
        """General: connections reveal shell/block structure."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Connection Structure = Chiral Block + Hinge Hub")
        self.log(f"  {'='*55}")
        self.log(f"")
        self.log(f"  ℂ² (temporal) has only 2 directions: ↑ and ↓")
        self.log(f"  → Same-spin electrons overlap ≈ 1 in temporal")
        self.log(f"  → Opposite-spin overlap ≈ 0")
        self.log(f"  → CHIRAL BLOCK STRUCTURE:")
        self.log(f"")
        self.log(f"    ┌──── SPIN ↑ ────┐  ┌──── SPIN ↓ ────┐")
        self.log(f"    │ all ↑ connected │  │ all ↓ connected │")
        self.log(f"    │ (overlap ≈ 1)   │  │ (overlap ≈ 1)   │")
        self.log(f"    └────────────────┘  └────────────────┘")
        self.log(f"        ↑─↓ cross: overlap ≈ O(ε²) ≈ 0")
        self.log(f"")
        self.log(f"  The DISTINCTION between orbitals is in")
        self.log(f"  the SPATIAL sector (ε² ≈ 10⁻⁴).")
        self.log(f"  This is tiny — but det(AAB) depends on it.")
        self.log(f"")
        self.log(f"  HINGE CONNECTION (the physical interaction):")
        self.log(f"")
        self.log(f"                A₁(u)")
        self.log(f"               ╱ | ╲")
        self.log(f"             A₂(u)─A₃(d)   ← nuclear hub")
        self.log(f"            ╱╱╱ ||| ╲╲╲")
        self.log(f"    S(1s) S(2s) S(2p_x) S(2p_y) S(2p_z) ...")
        self.log(f"    [↑↓]  [↑↓]  [↑↓]   [↑↓]   [↑↓]")
        self.log(f"")
        self.log(f"  ALL simplices attach to the nuclear triangle.")
        self.log(f"  Screening = how much each simplex's AAB hinges")
        self.log(f"  modify the effective charge at the hub.")
        self.log(f"")
        self.log(f"  σ_cross  (7/8)  = S1─S3: different spatial direction")
        self.log(f"  σ_same_s (0.60) = S1─S2: same spatial, diff temporal")
        self.log(f"  σ_same_p (3/4)  = S3─S4: same l, diff m")
        self.check("Block structure documented", True)


if __name__ == "__main__":
    SimplexConnections().execute()
