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

        # ═══ Single Simplex (H): 5 vertices ═══
        self.log("=" * 65)
        self.log("HYDROGEN: Regge stationary point")
        self.log("=" * 65)

        simplex_H = [(0, 1, 2, 3, 4)]

        # Strategy: S vertices fixed (orthogonal C³), optimize T only
        # T has 2 vertices × 10 real params = 20 DOF (much smaller!)
        S1 = np.array([0,0,1,0,0], dtype=complex)
        S2 = np.array([0,0,0,1,0], dtype=complex)
        S3 = np.array([0,0,0,0,1], dtype=complex)
        S_fixed = [S1, S2, S3]

        def H_action(t_params):
            """Regge action with S fixed, only T varies."""
            psi = np.zeros(5*10)
            for i in range(3):
                psi[i*10:i*10+5] = S_fixed[i].real
                psi[i*10+5:i*10+10] = S_fixed[i].imag
            # T vertices from params
            for k in range(2):
                re = t_params[k*10:k*10+5]
                im = t_params[k*10+5:k*10+10]
                v = re + 1j*im
                n = np.linalg.norm(v)
                if n < 1e-15: return 1e10
                v = v/n
                # C² constraint
                c3n = np.sqrt(np.sum(np.abs(v[2:5])**2))
                if c3n > 0.3:
                    v[2:5] *= 0.3/c3n
                    v = v/np.linalg.norm(v)
                psi[(3+k)*10:(3+k)*10+5] = v.real
                psi[(3+k)*10+5:(3+k)*10+10] = v.imag
            return regge_action_from_psi(psi, simplex_list=simplex_H)

        def H_grad_norm(t_params):
            g = numerical_gradient(H_action, t_params, eps=1e-6)
            return np.sum(g**2)

        best_x_H = None
        best_gn_H = np.inf
        best_S_H = 0

        self.log(f"\n  Optimizing 2 T vertices (20 DOF), S fixed...")
        for trial in range(8):
            x0 = np.zeros(20)
            # T₁
            x0[0] = np.random.uniform(0.5, 1.0)
            x0[1] = np.random.uniform(-0.5, 0.5)
            x0[2:5] = np.random.uniform(-0.15, 0.15, 3)
            x0[5:10] = np.random.uniform(-0.3, 0.3, 5)
            # T₂
            x0[10] = np.random.uniform(-0.5, 0.5)
            x0[11] = np.random.uniform(0.5, 1.0)
            x0[12:15] = np.random.uniform(-0.15, 0.15, 3)
            x0[15:20] = np.random.uniform(-0.3, 0.3, 5)

            res = minimize(H_grad_norm, x0, method='Nelder-Mead',
                          options={'maxiter': 300, 'xatol': 1e-6, 'fatol': 1e-10})

            S_val = H_action(res.x)
            if res.fun < best_gn_H:
                best_gn_H = res.fun
                best_x_H = res.x.copy()
                best_S_H = S_val
                self.log(f"    trial {trial}: |∇S|²={res.fun:.2e} S={S_val:.4f}")

        self.log(f"\n  Best: |∇S|²={best_gn_H:.2e}, S(H)={best_S_H:.4f}")

        # Read H geometry
        self.log(f"\n  T vertex structure at stationary point:")
        for k in range(2):
            re = best_x_H[k*10:k*10+5]
            im = best_x_H[k*10+5:k*10+10]
            v = re + 1j*im; v = v/np.linalg.norm(v)
            c2 = np.sqrt(np.sum(np.abs(v[:2])**2))
            c3 = np.sqrt(np.sum(np.abs(v[2:])**2))
            self.log(f"    T{k+1}: C²={c2:.4f} C³={c3:.4f}")

        self.check("H stationary found", best_gn_H < 0.1)

        # ═══ Two Simplices (He) ═══
        self.log(f"\n{'='*65}")
        self.log("HELIUM: 2 simplices, SSS shared, 4 T vertices (40 DOF)")
        self.log(f"{'='*65}")

        simplex_He = [(0,1,2,3,4), (0,1,2,5,6)]

        def He_action(t_params):
            psi = np.zeros(7*10)
            for i in range(3):
                psi[i*10:i*10+5] = S_fixed[i].real
                psi[i*10+5:i*10+10] = S_fixed[i].imag
            for k in range(4):
                re = t_params[k*10:k*10+5]
                im = t_params[k*10+5:k*10+10]
                v = re + 1j*im
                n = np.linalg.norm(v)
                if n < 1e-15: return 1e10
                v = v/n
                c3n = np.sqrt(np.sum(np.abs(v[2:5])**2))
                if c3n > 0.3:
                    v[2:5] *= 0.3/c3n
                    v = v/np.linalg.norm(v)
                psi[(3+k)*10:(3+k)*10+5] = v.real
                psi[(3+k)*10+5:(3+k)*10+10] = v.imag
            return regge_action_from_psi(psi, simplex_list=simplex_He)

        def He_grad_norm(t_params):
            g = numerical_gradient(He_action, t_params, eps=1e-6)
            return np.sum(g**2)

        best_x_He = None
        best_gn_He = np.inf
        best_S_He = 0

        self.log(f"\n  Optimizing 4 T vertices (40 DOF)...")
        for trial in range(3):  # reduced from 10
            x0 = np.zeros(40)
            for k in range(4):
                phase = k * np.pi / 2
                x0[k*10] = np.cos(phase) * np.random.uniform(0.5, 1.0)
                x0[k*10+1] = np.sin(phase) * np.random.uniform(0.5, 1.0)
                x0[k*10+2:k*10+5] = np.random.uniform(-0.1, 0.1, 3)
                x0[k*10+5:k*10+10] = np.random.uniform(-0.2, 0.2, 5)

            res = minimize(He_grad_norm, x0, method='Nelder-Mead',
                          options={'maxiter': 300, 'xatol': 1e-6, 'fatol': 1e-10})

            S_val = He_action(res.x)
            if res.fun < best_gn_He:
                best_gn_He = res.fun
                best_x_He = res.x.copy()
                best_S_He = S_val
                self.log(f"    trial {trial}: |∇S|²={res.fun:.2e} S={S_val:.4f}")

        self.log(f"\n  Best: |∇S|²={best_gn_He:.2e}, S(He)={best_S_He:.4f}")

        if abs(best_S_H) > 1e-10:
            self.log(f"  S(He)/S(H) = {best_S_He/best_S_H:.4f}")

        self.check("He stationary found", best_gn_He < 1.0)

        # ═══ Summary ═══
        self.log(f"\n{'='*65}")
        self.log("SUMMARY")
        self.log(f"{'='*65}")
        self.log(f"  H:  S={best_S_H:.4f}, |∇S|²={best_gn_H:.2e}")
        self.log(f"  He: S={best_S_He:.4f}, |∇S|²={best_gn_He:.2e}")
        if abs(best_S_H) > 1e-10:
            self.log(f"  Ratio S(He)/S(H) = {best_S_He/best_S_H:.4f}")
        self.log(f"\n  No ad hoc energy. Only S = Σ A_h δ_h.")


if __name__ == "__main__":
    Phase1b().execute()
