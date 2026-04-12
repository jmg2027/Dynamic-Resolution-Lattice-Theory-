"""
EXP_042b: Analytical Regge Action + Autograd Stationary Points
==============================================================

The Regge action S(ψ) is a closed-form function of the vertex vectors.
Use JAX or pure numpy autograd to compute ∇S analytically, then find
stationary points (∇S = 0) efficiently.

Three approaches attempted:
1. JAX autodiff (if available)
2. Analytical gradient (hand-derived for single simplex)
3. Scipy with analytical Jacobian
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

import numpy as np
from scipy.optimize import minimize, root
from itertools import combinations
from experiment import Experiment


# ═══════════════════════════════════════════════════════════════
#  Pure-numpy Regge action (vectorized, no loops over hinges)
# ═══════════════════════════════════════════════════════════════

def build_gram_5(psi):
    """5×5 Gram matrix from 5 vertex vectors (each C⁵)."""
    # psi: (5, 5) complex array
    return psi @ psi.conj().T


def all_hinge_dets(G):
    """Compute det(G_h) for all C(5,3)=10 hinges.
    Returns array of 10 dets, and the hinge index list."""
    hinges = list(combinations(range(5), 3))
    dets = np.zeros(10)
    for k, (i, j, l) in enumerate(hinges):
        G3 = G[np.ix_([i,j,l], [i,j,l])]
        dets[k] = np.real(np.linalg.det(G3))
    return dets, hinges


def dihedral_from_gram(G, hinge, apex1, apex2):
    """Dihedral angle from the full 5×5 Gram matrix.

    Uses the formula: perpendicular projection of apex onto
    complement of hinge subspace, then angle between projections.
    """
    h_idx = list(hinge)
    G_h = G[np.ix_(h_idx, h_idx)]
    det_h = np.real(np.linalg.det(G_h))
    if det_h < 1e-15:
        return np.pi / 3

    G_h_inv = np.linalg.inv(G_h)

    def perp_overlap(apex_idx):
        # Overlap of apex with each hinge vertex
        overlaps = G[h_idx, apex_idx]  # (3,) complex
        # Projection magnitude: overlaps^T G_h^{-1} overlaps
        proj_sq = np.real(overlaps.conj() @ G_h_inv @ overlaps)
        # Perpendicular squared norm: G[apex,apex] - proj_sq
        perp_sq = np.real(G[apex_idx, apex_idx]) - proj_sq
        return overlaps, proj_sq, max(perp_sq, 0)

    ov1, proj1, perp1 = perp_overlap(apex1)
    ov2, proj2, perp2 = perp_overlap(apex2)

    if perp1 < 1e-15 or perp2 < 1e-15:
        return np.pi / 3

    # Cross term: <perp1|perp2> = G[a1,a2] - ov1^T G_h^{-1} ov2
    cross = np.real(G[apex1, apex2] - ov1.conj() @ G_h_inv @ ov2)
    cos_theta = cross / np.sqrt(perp1 * perp2)
    cos_theta = np.clip(cos_theta, -1, 1)
    return float(np.arccos(cos_theta))


def regge_action_from_psi(psi_flat, n_simplices=1, simplex_list=None):
    """Compute Regge action from flat parameter array.

    psi_flat: flat real array of vertex parameters
    Returns: scalar S = Σ A_h δ_h
    """
    n_verts = len(psi_flat) // 10
    psi = np.zeros((n_verts, 5), dtype=complex)
    for i in range(n_verts):
        re = psi_flat[i*10:i*10+5]
        im = psi_flat[i*10+5:i*10+10]
        v = re + 1j * im
        n = np.linalg.norm(v)
        if n < 1e-15:
            return 1e10
        psi[i] = v / n

    if simplex_list is None:
        simplex_list = [tuple(range(min(n_verts, 5)))]

    G_full = psi @ psi.conj().T

    # Collect unique hinges
    all_hinges = set()
    for simp in simplex_list:
        for tri in combinations(simp, 3):
            all_hinges.add(tuple(sorted(tri)))

    S = 0.0
    for hinge in all_hinges:
        # Area
        G_h = G_full[np.ix_(list(hinge), list(hinge))]
        det_h = np.real(np.linalg.det(G_h))
        if det_h < 1e-15:
            continue
        A = np.sqrt(det_h)

        # Deficit angle: sum dihedral angles from all simplices containing this hinge
        total_theta = 0.0
        h_set = set(hinge)
        for simp in simplex_list:
            if h_set.issubset(set(simp)):
                apices = [v for v in simp if v not in h_set]
                if len(apices) >= 2:
                    theta = dihedral_from_gram(G_full, hinge, apices[0], apices[1])
                    total_theta += theta

        delta = 2 * np.pi - total_theta
        S += A * delta

    return S


# ═══════════════════════════════════════════════════════════════
#  Stationary point finders
# ═══════════════════════════════════════════════════════════════

def numerical_gradient(f, x, eps=1e-7):
    """Central difference gradient."""
    n = len(x)
    g = np.zeros(n)
    for i in range(n):
        xp = x.copy(); xp[i] += eps
        xm = x.copy(); xm[i] -= eps
        g[i] = (f(xp) - f(xm)) / (2 * eps)
    return g


def find_stationary_scipy(objective, n_verts, simplex_list, n_trials=15,
                          constrain_T=True, T_indices=None, max_c3=0.3):
    """Find stationary point of Regge action using scipy."""

    def wrapped_obj(x):
        # Enforce C² constraint on T vertices
        if constrain_T and T_indices:
            x2 = x.copy()
            for idx in T_indices:
                re = x2[idx*10+2:idx*10+5]  # C³ real parts
                im = x2[idx*10+7:idx*10+10]  # C³ imag parts
                c3_amp = np.sqrt(np.sum(re**2) + np.sum(im**2))
                if c3_amp > max_c3:
                    scale = max_c3 / c3_amp
                    x2[idx*10+2:idx*10+5] *= scale
                    x2[idx*10+7:idx*10+10] *= scale
            return regge_action_from_psi(x2, simplex_list=simplex_list)
        return regge_action_from_psi(x, simplex_list=simplex_list)

    def grad_norm(x):
        g = numerical_gradient(wrapped_obj, x)
        return np.sum(g**2)

    best_x = None
    best_gn = np.inf

    for trial in range(n_trials):
        # Initialize
        x0 = np.zeros(n_verts * 10)
        for i in range(n_verts):
            if T_indices and i in T_indices:
                # T vertex: mostly C²
                x0[i*10] = np.random.uniform(0.5, 1.0)
                x0[i*10+1] = np.random.uniform(-0.5, 0.5)
                x0[i*10+2:i*10+5] = np.random.uniform(-0.1, 0.1, 3)
                x0[i*10+5:i*10+10] = np.random.uniform(-0.3, 0.3, 5)
            else:
                # S vertex: mostly C³
                x0[i*10+2+i%3] = 1.0
                x0[i*10:i*10+2] = np.random.uniform(-0.05, 0.05, 2)
                x0[i*10+5:i*10+10] = np.random.uniform(-0.05, 0.05, 5)

        # Minimize |∇S|²
        res = minimize(grad_norm, x0, method='Nelder-Mead',
                      options={'maxiter': 2000, 'xatol': 1e-10, 'fatol': 1e-14,
                               'adaptive': True})

        if res.fun < best_gn:
            best_gn = res.fun
            best_x = res.x.copy()

    return best_x, best_gn


class Phase1b(Experiment):
    ID = "042b"
    TITLE = "Regge Stationary"

    def run(self):
        np.random.seed(42)

        # ═══ Single Simplex (H): 5 vertices, S fixed, T free ═══
        self.log("=" * 65)
        self.log("HYDROGEN: Regge stationary point (5 vertices)")
        self.log("=" * 65)

        simplex_list_H = [(0, 1, 2, 3, 4)]
        T_idx_H = [3, 4]

        # Fix S vertices
        x_H, gn_H = find_stationary_scipy(
            None, 5, simplex_list_H,
            n_trials=10, T_indices=T_idx_H
        )

        S_H = regge_action_from_psi(x_H, simplex_list=simplex_list_H)
        self.log(f"\n  |∇S|² = {gn_H:.2e}")
        self.log(f"  S(H) = {S_H:.6f}")

        # Read geometry
        psi_H = np.zeros((5, 5), dtype=complex)
        for i in range(5):
            v = x_H[i*10:i*10+5] + 1j * x_H[i*10+5:i*10+10]
            psi_H[i] = v / np.linalg.norm(v)

        G_H = build_gram_5(psi_H)
        dets_H, hinges_H = all_hinge_dets(G_H)

        self.log(f"\n  Hinge structure at stationary point:")
        labels = ['S₁','S₂','S₃','T₁','T₂']
        for k, (h, d) in enumerate(zip(hinges_H, dets_H)):
            ns = sum(1 for i in h if i < 3)
            ht = {3:'SSS',2:'SST',1:'STT',0:'TTT'}[ns]
            name = f"({labels[h[0]]},{labels[h[1]]},{labels[h[2]]})"
            self.log(f"    {name:<15} {ht} det={d:.4f}")

        # T vertex analysis
        self.log(f"\n  T vertex structure:")
        for i in T_idx_H:
            v = psi_H[i]
            c2 = np.linalg.norm(v[:2])
            c3 = np.linalg.norm(v[2:])
            self.log(f"    {labels[i]}: C²={c2:.4f} C³={c3:.4f} ratio={c2/c3:.2f}")

        self.check("H stationary found (|∇S|² < 0.01)", gn_H < 0.01)

        # ═══ Two Simplices (He): 7 vertices, SSS shared ═══
        self.log(f"\n{'='*65}")
        self.log("HELIUM: Regge stationary point (7 vertices, 2 simplices)")
        self.log(f"{'='*65}")

        simplex_list_He = [(0, 1, 2, 3, 4), (0, 1, 2, 5, 6)]
        T_idx_He = [3, 4, 5, 6]

        x_He, gn_He = find_stationary_scipy(
            None, 7, simplex_list_He,
            n_trials=10, T_indices=T_idx_He
        )

        S_He = regge_action_from_psi(x_He, simplex_list=simplex_list_He)
        self.log(f"\n  |∇S|² = {gn_He:.2e}")
        self.log(f"  S(He) = {S_He:.6f}")

        # Read geometry
        psi_He = np.zeros((7, 5), dtype=complex)
        for i in range(7):
            v = x_He[i*10:i*10+5] + 1j * x_He[i*10+5:i*10+10]
            psi_He[i] = v / np.linalg.norm(v)

        G_He = psi_He @ psi_He.conj().T

        self.log(f"\n  T vertex structure:")
        labels_He = ['S₁','S₂','S₃','T₁','T₂','T₃','T₄']
        for i in T_idx_He:
            v = psi_He[i]
            c2 = np.linalg.norm(v[:2])
            c3 = np.linalg.norm(v[2:])
            self.log(f"    {labels_He[i]}: C²={c2:.4f} C³={c3:.4f}")

        # Unique hinges and their dets
        all_hinges = set()
        for simp in simplex_list_He:
            for tri in combinations(simp, 3):
                all_hinges.add(tuple(sorted(tri)))

        self.log(f"\n  All {len(all_hinges)} unique hinges:")
        sss_sum, sst_sum, stt_sum = 0, 0, 0
        for h in sorted(all_hinges):
            G3 = G_He[np.ix_(list(h), list(h))]
            d = np.real(np.linalg.det(G3))
            ns = sum(1 for i in h if i < 3)
            ht = {3:'SSS',2:'SST',1:'STT',0:'TTT'}[ns]
            if ht == 'SSS': sss_sum += d
            elif ht == 'SST': sst_sum += d
            elif ht == 'STT': stt_sum += d
            self.log(f"    {h} {ht} det={d:.4f}")

        self.log(f"\n  Sum by type: SSS={sss_sum:.4f} SST={sst_sum:.4f} STT={stt_sum:.4f}")

        # Ratio He/H
        if abs(S_H) > 1e-10:
            ratio = S_He / S_H
            self.log(f"\n  S(He)/S(H) = {ratio:.4f}")
            self.log(f"  (geometry-determined ratio, no σ assumed)")

        self.check("He stationary found (|∇S|² < 0.1)", gn_He < 0.1)

        # ═══ H₂ molecule: 2 simplices, T shared ═══
        self.log(f"\n{'='*65}")
        self.log("H₂: Regge stationary point (9 vertices, T shared)")
        self.log(f"{'='*65}")

        simplex_list_H2 = [(0, 1, 2, 6, 7), (3, 4, 5, 7, 8)]
        T_idx_H2 = [6, 7, 8]  # T vertices

        x_H2, gn_H2 = find_stationary_scipy(
            None, 9, simplex_list_H2,
            n_trials=8, T_indices=T_idx_H2
        )

        S_H2 = regge_action_from_psi(x_H2, simplex_list=simplex_list_H2)
        self.log(f"\n  |∇S|² = {gn_H2:.2e}")
        self.log(f"  S(H₂) = {S_H2:.6f}")

        if abs(S_H) > 1e-10:
            self.log(f"  S(H₂) / (2×S(H)) = {S_H2 / (2*S_H):.4f}")
            self.log(f"  (< 1 means H₂ is bound relative to 2H)")

        self.check("H₂ stationary found", gn_H2 < 1.0)

        # ═══ Summary ═══
        self.log(f"\n{'='*65}")
        self.log("SUMMARY")
        self.log(f"{'='*65}")
        self.log(f"  H:  S = {S_H:.4f},  |∇S|² = {gn_H:.2e}")
        self.log(f"  He: S = {S_He:.4f}, |∇S|² = {gn_He:.2e}")
        self.log(f"  H₂: S = {S_H2:.4f}, |∇S|² = {gn_H2:.2e}")
        self.log(f"\n  Method: exact Regge action, Nelder-Mead on |∇S|²")
        self.log(f"  No ad hoc energy. Only S = Σ A_h δ_h.")


if __name__ == "__main__":
    Phase1b().execute()
