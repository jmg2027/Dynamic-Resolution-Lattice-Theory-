"""
simplex_builder.py — Build atomic simplex structures
=====================================================

Each atom = Z simplices sharing SSS core.
Vertex types: S (C³ dominated) and T (C² dominated).
T vertices constrained to C² (max C³ leak = 0.3).
"""

import numpy as np
from regge_core import set_vertex_types


def normalize(v):
    n = np.linalg.norm(v)
    return v / n if n > 1e-15 else v


def make_S_vertex(direction, perturbation=0.02):
    """S-type vertex: mostly C³ (indices 2,3,4), small C² admixture."""
    psi = np.zeros(5, dtype=complex)
    psi[2 + direction] = 1.0  # dominant spatial component
    psi += perturbation * (np.random.randn(5) + 1j * np.random.randn(5))
    return normalize(psi)


def make_T_vertex(c2_angles, c3_leak=0.1):
    """T-type vertex: mostly C² (indices 0,1), small C³ leak.

    c2_angles: (θ, φ) parameterizing the C² direction
    c3_leak: total C³ amplitude (constrained < 0.3)
    """
    c3_leak = min(abs(c3_leak), 0.3)
    psi = np.zeros(5, dtype=complex)
    # C² part (dominant)
    c2_amp = np.sqrt(1 - c3_leak**2)
    psi[0] = c2_amp * np.cos(c2_angles[0]) * np.exp(1j * c2_angles[1])
    psi[1] = c2_amp * np.sin(c2_angles[0])
    # C³ leak (small, equal in all 3 directions)
    psi[2] = c3_leak / np.sqrt(3)
    psi[3] = c3_leak / np.sqrt(3)
    psi[4] = c3_leak / np.sqrt(3)
    return normalize(psi)


def build_hydrogen(epsilon=0.1):
    """Hydrogen: 1 simplex = {S₁, S₂, S₃, T₁, T₂}

    Returns: (all_vecs, simplex_list, vertex_types)
    """
    all_vecs = {
        0: make_S_vertex(0),  # S₁
        1: make_S_vertex(1),  # S₂
        2: make_S_vertex(2),  # S₃
        3: make_T_vertex((0.3, 0.0), c3_leak=epsilon),  # T₁ (electron)
        4: make_T_vertex((1.2, 0.5), c3_leak=epsilon),  # T₂ (available slot)
    }
    simplex_list = [(0, 1, 2, 3, 4)]
    vtypes = {0: 'S', 1: 'S', 2: 'S', 3: 'T', 4: 'T'}
    set_vertex_types(vtypes)
    return all_vecs, simplex_list, vtypes


def build_helium(epsilon=0.1):
    """Helium: 2 simplices sharing SSS face.

    Simplex A: {S₁, S₂, S₃, T₁, T₂}
    Simplex B: {S₁, S₂, S₃, T₃, T₄}

    6 unique vertices: 3S + 4T.
    """
    all_vecs = {
        0: make_S_vertex(0),  # S₁
        1: make_S_vertex(1),  # S₂
        2: make_S_vertex(2),  # S₃
        3: make_T_vertex((0.3, 0.0), c3_leak=epsilon),  # T₁ (e₁ ↑)
        4: make_T_vertex((1.2, 0.5), c3_leak=epsilon),  # T₂ (slot for e₁)
        5: make_T_vertex((0.3, np.pi), c3_leak=epsilon),  # T₃ (e₂ ↓)
        6: make_T_vertex((1.2, np.pi+0.5), c3_leak=epsilon),  # T₄ (slot for e₂)
    }
    simplex_list = [
        (0, 1, 2, 3, 4),  # simplex A
        (0, 1, 2, 5, 6),  # simplex B
    ]
    vtypes = {0: 'S', 1: 'S', 2: 'S', 3: 'T', 4: 'T', 5: 'T', 6: 'T'}
    set_vertex_types(vtypes)
    return all_vecs, simplex_list, vtypes


def build_h2_molecule(epsilon=0.1):
    """H₂: 2 simplices sharing T vertex (covalent bond).

    Simplex A: {S₁, S₂, S₃, T₁, T_shared}
    Simplex B: {S₄, S₅, S₆, T₂, T_shared}

    T_shared = vertex 7, shared between both = covalent bond.
    """
    all_vecs = {
        0: make_S_vertex(0),
        1: make_S_vertex(1),
        2: make_S_vertex(2),
        3: make_S_vertex(0, perturbation=0.05),  # S₄ (different proton)
        4: make_S_vertex(1, perturbation=0.05),
        5: make_S_vertex(2, perturbation=0.05),
        6: make_T_vertex((0.3, 0.0), c3_leak=epsilon),   # T₁
        7: make_T_vertex((0.8, 0.3), c3_leak=epsilon),   # T_shared (bond!)
        8: make_T_vertex((1.2, 0.5), c3_leak=epsilon),   # T₂
    }
    simplex_list = [
        (0, 1, 2, 6, 7),  # H atom A
        (3, 4, 5, 7, 8),  # H atom B (shares vertex 7)
    ]
    vtypes = {i: 'S' for i in range(6)}
    vtypes.update({6: 'T', 7: 'T', 8: 'T'})
    set_vertex_types(vtypes)
    return all_vecs, simplex_list, vtypes


def pack_params(all_vecs, free_indices):
    """Pack free vertex parameters into flat array for optimization."""
    params = []
    for idx in free_indices:
        v = all_vecs[idx]
        params.extend(v.real)
        params.extend(v.imag)
    return np.array(params)


def unpack_params(params, all_vecs, free_indices, vtypes, max_c3=0.3):
    """Unpack flat array back to vertex dict with C² constraint."""
    new_vecs = dict(all_vecs)
    for k, idx in enumerate(free_indices):
        re = params[k*10 : k*10+5]
        im = params[k*10+5 : k*10+10]
        v = re + 1j * im
        v = normalize(v)

        # Enforce C² constraint for T vertices
        if vtypes.get(idx, 'S') == 'T':
            c3_norm = np.linalg.norm(v[2:5])
            if c3_norm > max_c3:
                v[2:5] *= max_c3 / c3_norm
                v = normalize(v)

        new_vecs[idx] = v
    return new_vecs
