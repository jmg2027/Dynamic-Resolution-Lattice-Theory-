"""
regge_core.py — Exact DRLT Regge Calculus
==========================================

No ad hoc energy functions. Only:
  G_ij = ⟨ψ_i|ψ_j⟩
  A_h = √det(G_h)
  δ_h = 2π - Σ θ_dihedral
  S = Σ A_h × δ_h

Everything from the Gram matrix. Nothing else.
"""

import numpy as np
from itertools import combinations


# ═══════════════════════════════════════════════════════════════
#  Fundamental: G, det, area
# ═══════════════════════════════════════════════════════════════

def overlap(a, b):
    """G_ij = ⟨ψ_i|ψ_j⟩"""
    return complex(np.vdot(a, b))


def gram_matrix(vecs):
    """G for a set of vectors. G_ij = ⟨ψ_i|ψ_j⟩."""
    n = len(vecs)
    G = np.zeros((n, n), dtype=complex)
    for i in range(n):
        for j in range(n):
            G[i, j] = np.vdot(vecs[i], vecs[j])
    return G


def hinge_det(v1, v2, v3):
    """det(G_h) for hinge triangle {v1, v2, v3}."""
    G = gram_matrix([v1, v2, v3])
    return float(np.real(np.linalg.det(G)))


def hinge_area(v1, v2, v3):
    """A_h = √det(G_h). Returns 0 if det < 0."""
    d = hinge_det(v1, v2, v3)
    return np.sqrt(max(d, 0.0))


# ═══════════════════════════════════════════════════════════════
#  Dihedral angle: the EXACT formula
# ═══════════════════════════════════════════════════════════════

def dihedral_angle(hinge_vecs, apex1, apex2):
    """Dihedral angle at a hinge between two tetrahedra.

    hinge_vecs: list of 3 vectors [v1, v2, v3] forming the hinge
    apex1, apex2: the two apex vertices (one per tetrahedron)

    Method: project each apex perpendicular to the hinge plane,
    then compute the angle between the projections.
    """
    G_h = gram_matrix(hinge_vecs)
    det_h = np.real(np.linalg.det(G_h))

    if det_h < 1e-15:
        return np.pi / 3  # degenerate hinge, return default

    G_inv = np.linalg.inv(G_h)

    def perp_component(apex):
        """Project apex perpendicular to the hinge subspace."""
        # overlaps of apex with hinge vectors
        overlaps = np.array([np.vdot(h, apex) for h in hinge_vecs])
        # projection onto hinge subspace
        proj = np.zeros(5, dtype=complex)
        for i in range(3):
            for j in range(3):
                proj += G_inv[i, j] * overlaps[j] * hinge_vecs[i]
        # perpendicular = apex - projection
        return apex - proj

    p1 = perp_component(apex1)
    p2 = perp_component(apex2)

    n1 = np.linalg.norm(p1)
    n2 = np.linalg.norm(p2)

    if n1 < 1e-15 or n2 < 1e-15:
        return np.pi / 3  # degenerate

    cos_theta = np.real(np.vdot(p1, p2)) / (n1 * n2)
    cos_theta = np.clip(cos_theta, -1.0, 1.0)

    return float(np.arccos(cos_theta))


# ═══════════════════════════════════════════════════════════════
#  Deficit angle and Regge action
# ═══════════════════════════════════════════════════════════════

def deficit_angle(hinge_vecs, simplex_list, hinge_indices):
    """Compute deficit angle at a hinge.

    hinge_indices: tuple of 3 vertex indices forming the hinge
    simplex_list: list of simplices (each = list of 5 vertex indices)

    Finds all simplices containing this hinge,
    computes dihedral angle for each adjacent pair,
    returns δ = 2π - Σθ.
    """
    h_set = set(hinge_indices)

    # Find simplices containing this hinge
    containing = []
    for simp in simplex_list:
        if h_set.issubset(set(simp)):
            containing.append(simp)

    if len(containing) < 1:
        return 0.0  # isolated hinge

    # For each simplex containing the hinge, find the 2 apices
    # and compute the dihedral angle
    total_angle = 0.0
    for simp in containing:
        apices = [v for v in simp if v not in h_set]
        if len(apices) == 2:
            # Get actual vectors
            h_vecs = [hinge_vecs[i] for i in hinge_indices]
            a1 = hinge_vecs[apices[0]]
            a2 = hinge_vecs[apices[1]]
            theta = dihedral_angle(h_vecs, a1, a2)
            total_angle += theta

    return 2 * np.pi - total_angle


def regge_action(all_vecs, simplex_list):
    """Compute total Regge action S = Σ A_h × δ_h.

    all_vecs: dict or list of all vertex vectors {index: ψ}
    simplex_list: list of simplices (each = tuple of 5 vertex indices)

    Returns: total action, and per-hinge breakdown.
    """
    # Collect all unique hinges
    all_hinges = set()
    for simp in simplex_list:
        for tri in combinations(simp, 3):
            all_hinges.add(tuple(sorted(tri)))

    S_total = 0.0
    breakdown = []

    for hinge_idx in all_hinges:
        # Hinge vectors
        h_vecs = [all_vecs[i] for i in hinge_idx]

        # Area
        A = hinge_area(h_vecs[0], h_vecs[1], h_vecs[2])
        if A < 1e-15:
            continue

        # Deficit angle
        delta = deficit_angle(all_vecs, simplex_list, hinge_idx)

        # Classify
        htype = classify_hinge(hinge_idx)

        # Regge contribution
        S_h = A * delta
        S_total += S_h

        breakdown.append({
            'hinge': hinge_idx,
            'type': htype,
            'det': hinge_det(h_vecs[0], h_vecs[1], h_vecs[2]),
            'area': A,
            'deficit': delta,
            'action': S_h,
        })

    return S_total, breakdown


# ═══════════════════════════════════════════════════════════════
#  Hinge classification
# ═══════════════════════════════════════════════════════════════

# Global vertex type map (set by simplex_builder)
_vertex_types = {}


def set_vertex_types(type_map):
    """Set the global vertex type map. type_map: {index: 'S' or 'T'}"""
    global _vertex_types
    _vertex_types = type_map


def classify_hinge(hinge_indices):
    """Classify hinge as SSS/SST/STT/TTT."""
    n_s = sum(1 for i in hinge_indices if _vertex_types.get(i, 'S') == 'S')
    return {3: 'SSS', 2: 'SST', 1: 'STT', 0: 'TTT'}[n_s]


# ═══════════════════════════════════════════════════════════════
#  S/ħ computation
# ═══════════════════════════════════════════════════════════════

def action_over_hbar(all_vecs, simplex_list):
    """S/ħ = 4ln2 × Σ δ_h (area cancels!).

    This is the UV-finite, scale-free quantity.
    """
    all_hinges = set()
    for simp in simplex_list:
        for tri in combinations(simp, 3):
            all_hinges.add(tuple(sorted(tri)))

    total = 0.0
    for hinge_idx in all_hinges:
        delta = deficit_angle(all_vecs, simplex_list, hinge_idx)
        total += delta

    return 4 * np.log(2) * total
