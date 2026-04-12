"""
EXP_042 Phase 1b: Regge Stationary Points via JAX Autodiff
==========================================================

Goal: Find δS/δψ = 0 (stationary point, NOT minimum) for
- Hydrogen (1 simplex, 5 vertices)
- Helium (2 simplices, 7 vertices, shared SSS)
- H₂O (if time permits)

Uses JAX for automatic differentiation of the Regge action.
Key: STATIONARY point (gradient = 0), not minimum.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

import numpy as np
import jax
import jax.numpy as jnp
from itertools import combinations

jax.config.update("jax_enable_x64", True)

print("=" * 60)
print("EXP_042 Phase 1b: Regge Stationary Points (JAX)")
print("=" * 60)


# ═══════════════════════════════════════════════════════════════
#  Regge calculus in JAX (differentiable)
# ═══════════════════════════════════════════════════════════════

def gram_3x3(v1, v2, v3):
    """3×3 Gram matrix for hinge triangle."""
    vecs = jnp.stack([v1, v2, v3])  # (3, 5) complex
    return vecs @ vecs.conj().T     # (3, 3)


def hinge_area_jax(v1, v2, v3):
    """A_h = √max(det(G_h), 0)."""
    G = gram_3x3(v1, v2, v3)
    d = jnp.real(jnp.linalg.det(G))
    return jnp.sqrt(jnp.maximum(d, 1e-30))


def dihedral_angle_jax(h1, h2, h3, apex1, apex2):
    """Dihedral angle at hinge {h1,h2,h3} between apices."""
    G_h = gram_3x3(h1, h2, h3)
    det_h = jnp.real(jnp.linalg.det(G_h))

    # Regularize for gradient stability
    G_reg = G_h + 1e-12 * jnp.eye(3, dtype=G_h.dtype)
    G_inv = jnp.linalg.inv(G_reg)

    hvecs = [h1, h2, h3]

    def perp_component(apex):
        overlaps = jnp.array([jnp.vdot(h, apex) for h in hvecs])
        proj = jnp.zeros(5, dtype=jnp.complex128)
        for i in range(3):
            for j in range(3):
                proj = proj + G_inv[i, j] * overlaps[j] * hvecs[i]
        return apex - proj

    p1 = perp_component(apex1)
    p2 = perp_component(apex2)

    n1 = jnp.linalg.norm(p1) + 1e-30
    n2 = jnp.linalg.norm(p2) + 1e-30

    cos_theta = jnp.real(jnp.vdot(p1, p2)) / (n1 * n2)
    cos_theta = jnp.clip(cos_theta, -1.0 + 1e-7, 1.0 - 1e-7)

    return jnp.arccos(cos_theta)


def regge_action_single_simplex(psi_flat):
    """Regge action for a single 4-simplex.

    psi_flat: (50,) real array = [Re(ψ₀), Im(ψ₀), Re(ψ₁), ..., Im(ψ₄)]
    Each ψ ∈ C⁵, so 5 complex = 10 real per vertex, × 5 vertices = 50.
    """
    # Unpack and normalize
    vecs = []
    for i in range(5):
        re = psi_flat[i*10 : i*10+5]
        im = psi_flat[i*10+5 : i*10+10]
        v = re + 1j * im
        v = v / (jnp.linalg.norm(v) + 1e-30)
        vecs.append(v)

    # All 10 hinges of a 4-simplex
    S = 0.0
    for tri in combinations(range(5), 3):
        i, j, k = tri
        A = hinge_area_jax(vecs[i], vecs[j], vecs[k])

        # The two apices are the remaining 2 vertices
        remaining = [x for x in range(5) if x not in tri]
        a1, a2 = remaining

        theta = dihedral_angle_jax(vecs[i], vecs[j], vecs[k],
                                    vecs[a1], vecs[a2])
        delta = 2 * jnp.pi - theta  # single simplex: 1 tet around each hinge
        S = S + A * delta

    return S


def regge_action_two_simplices(psi_flat, n_verts=7):
    """Regge action for 2 simplices sharing SSS face (Helium).

    Vertices: 0,1,2 = S (shared), 3,4 = T (simplex A), 5,6 = T (simplex B)
    """
    vecs = []
    for i in range(n_verts):
        re = psi_flat[i*10 : i*10+5]
        im = psi_flat[i*10+5 : i*10+10]
        v = re + 1j * im
        v = v / (jnp.linalg.norm(v) + 1e-30)
        vecs.append(v)

    simplex_list = [(0,1,2,3,4), (0,1,2,5,6)]

    # Collect all unique hinges
    all_hinges = set()
    for simp in simplex_list:
        for tri in combinations(simp, 3):
            all_hinges.add(tuple(sorted(tri)))

    S = 0.0
    for hinge in all_hinges:
        i, j, k = hinge
        A = hinge_area_jax(vecs[i], vecs[j], vecs[k])

        # Find simplices containing this hinge
        total_angle = 0.0
        for simp in simplex_list:
            if set(hinge).issubset(set(simp)):
                remaining = [x for x in simp if x not in hinge]
                if len(remaining) == 2:
                    theta = dihedral_angle_jax(vecs[i], vecs[j], vecs[k],
                                               vecs[remaining[0]], vecs[remaining[1]])
                    total_angle = total_angle + theta

        delta = 2 * jnp.pi - total_angle
        S = S + A * delta

    return S


# ═══════════════════════════════════════════════════════════════
#  C² constraint enforcement
# ═══════════════════════════════════════════════════════════════

def enforce_constraints(psi_flat, vertex_types, max_c3=0.3):
    """Project T vertices to satisfy C² constraint."""
    psi = np.array(psi_flat)
    n_verts = len(vertex_types)
    for i in range(n_verts):
        re = psi[i*10 : i*10+5]
        im = psi[i*10+5 : i*10+10]
        v = re + 1j * im
        norm = np.linalg.norm(v)
        if norm > 1e-15:
            v /= norm

        if vertex_types[i] == 'T':
            c3_norm = np.linalg.norm(v[2:5])
            if c3_norm > max_c3:
                v[2:5] *= max_c3 / c3_norm
                v /= np.linalg.norm(v)

        psi[i*10 : i*10+5] = v.real
        psi[i*10+5 : i*10+10] = v.imag
    return psi


# ═══════════════════════════════════════════════════════════════
#  Stationary point finder
# ═══════════════════════════════════════════════════════════════

def find_stationary_point(action_fn, psi_init, vertex_types,
                          lr=0.001, max_iter=5000, tol=1e-6):
    """Find stationary point δS/δψ = 0 by minimizing |∇S|².

    Key insight: we DON'T minimize S. We minimize |grad(S)|².
    """
    grad_S = jax.grad(action_fn)

    def grad_norm_sq(psi_flat):
        g = grad_S(psi_flat)
        return jnp.sum(g**2)

    grad_of_grad_norm = jax.grad(grad_norm_sq)

    psi = np.array(psi_init, dtype=np.float64)
    best_gn = float('inf')
    best_psi = psi.copy()

    print(f"  Initial S = {float(action_fn(jnp.array(psi))):.6f}")
    print(f"  Initial |∇S|² = {float(grad_norm_sq(jnp.array(psi))):.6f}")

    for step in range(max_iter):
        psi_jax = jnp.array(psi)
        gn = float(grad_norm_sq(psi_jax))

        if gn < best_gn:
            best_gn = gn
            best_psi = psi.copy()

        if gn < tol:
            print(f"  Converged at step {step}: |∇S|² = {gn:.2e}")
            break

        # Gradient descent on |∇S|²
        g = np.array(grad_of_grad_norm(psi_jax))
        psi = psi - lr * g

        # Enforce constraints
        psi = enforce_constraints(psi, vertex_types)

        if step % 500 == 0:
            S_val = float(action_fn(psi_jax))
            print(f"  Step {step:5d}: S = {S_val:.6f}, |∇S|² = {gn:.2e}")

    # Final
    psi_jax = jnp.array(best_psi)
    S_final = float(action_fn(psi_jax))
    gn_final = float(grad_norm_sq(psi_jax))
    print(f"  Final: S = {S_final:.6f}, |∇S|² = {gn_final:.2e}")
    return best_psi, S_final, gn_final


# ═══════════════════════════════════════════════════════════════
#  Build initial configurations
# ═══════════════════════════════════════════════════════════════

def init_hydrogen(epsilon=0.1):
    """Initialize hydrogen simplex."""
    np.random.seed(42)
    vecs = {}
    # S vertices: mostly C³
    for i, d in enumerate([0, 1, 2]):
        psi = np.zeros(5, dtype=complex)
        psi[2 + d] = 1.0
        psi += 0.02 * (np.random.randn(5) + 1j * np.random.randn(5))
        vecs[i] = psi / np.linalg.norm(psi)

    # T vertices: mostly C²
    for i, (theta, phi) in [(3, (0.3, 0.0)), (4, (1.2, 0.5))]:
        psi = np.zeros(5, dtype=complex)
        c2_amp = np.sqrt(1 - epsilon**2)
        psi[0] = c2_amp * np.cos(theta) * np.exp(1j * phi)
        psi[1] = c2_amp * np.sin(theta)
        psi[2:5] = epsilon / np.sqrt(3)
        vecs[i] = psi / np.linalg.norm(psi)

    vtypes = ['S', 'S', 'S', 'T', 'T']

    # Pack into flat array
    flat = []
    for i in range(5):
        flat.extend(vecs[i].real)
        flat.extend(vecs[i].imag)
    return np.array(flat), vtypes


def init_helium(epsilon=0.1):
    """Initialize helium: 2 simplices, shared SSS."""
    np.random.seed(42)
    vecs = {}
    for i, d in enumerate([0, 1, 2]):
        psi = np.zeros(5, dtype=complex)
        psi[2 + d] = 1.0
        psi += 0.02 * (np.random.randn(5) + 1j * np.random.randn(5))
        vecs[i] = psi / np.linalg.norm(psi)

    t_params = [(0.3, 0.0), (1.2, 0.5), (0.3, np.pi), (1.2, np.pi + 0.5)]
    for i, (theta, phi) in enumerate(t_params):
        psi = np.zeros(5, dtype=complex)
        c2_amp = np.sqrt(1 - epsilon**2)
        psi[0] = c2_amp * np.cos(theta) * np.exp(1j * phi)
        psi[1] = c2_amp * np.sin(theta)
        psi[2:5] = epsilon / np.sqrt(3)
        vecs[3 + i] = psi / np.linalg.norm(psi)

    vtypes = ['S', 'S', 'S', 'T', 'T', 'T', 'T']

    flat = []
    for i in range(7):
        flat.extend(vecs[i].real)
        flat.extend(vecs[i].imag)
    return np.array(flat), vtypes


# ═══════════════════════════════════════════════════════════════
#  Main experiment
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    results = {}

    # ── Phase 1b-1: Hydrogen ──────────────────────────────────
    print("\n" + "═" * 60)
    print("HYDROGEN (1 simplex, 5 vertices, 50 DOF)")
    print("═" * 60)

    psi_H, vtypes_H = init_hydrogen(epsilon=0.1)
    print("Compiling JAX... (first call is slow)")
    # Warm up JIT
    _ = regge_action_single_simplex(jnp.array(psi_H))
    print("JIT compiled.")

    psi_H_opt, S_H, gn_H = find_stationary_point(
        regge_action_single_simplex, psi_H, vtypes_H,
        lr=0.0005, max_iter=5000, tol=1e-8
    )
    results['H'] = {'S': S_H, 'grad_norm_sq': gn_H}

    # Analyze hinge structure at stationary point
    print("\nHinge analysis at stationary point:")
    vecs_H = []
    for i in range(5):
        re = psi_H_opt[i*10:i*10+5]
        im = psi_H_opt[i*10+5:i*10+10]
        v = re + 1j * im
        v /= np.linalg.norm(v)
        vecs_H.append(v)

    vtypes_map = {0: 'S', 1: 'S', 2: 'S', 3: 'T', 4: 'T'}
    for tri in combinations(range(5), 3):
        i, j, k = tri
        det_val = float(np.real(np.linalg.det(
            np.array([[np.vdot(vecs_H[a], vecs_H[b]) for b in tri] for a in tri])
        )))
        n_s = sum(1 for x in tri if vtypes_map[x] == 'S')
        htype = {3: 'SSS', 2: 'SST', 1: 'STT', 0: 'TTT'}[n_s]
        print(f"  {htype} {tri}: det = {det_val:.6f}")

    # ── Phase 1b-2: Helium ────────────────────────────────────
    print("\n" + "═" * 60)
    print("HELIUM (2 simplices, 7 vertices, 70 DOF)")
    print("═" * 60)

    psi_He, vtypes_He = init_helium(epsilon=0.1)
    print("Compiling JAX...")
    _ = regge_action_two_simplices(jnp.array(psi_He))
    print("JIT compiled.")

    psi_He_opt, S_He, gn_He = find_stationary_point(
        regge_action_two_simplices, psi_He, vtypes_He,
        lr=0.0003, max_iter=5000, tol=1e-8
    )
    results['He'] = {'S': S_He, 'grad_norm_sq': gn_He}

    # ── Summary ───────────────────────────────────────────────
    print("\n" + "═" * 60)
    print("SUMMARY")
    print("═" * 60)

    print(f"\n  Hydrogen:  S = {results['H']['S']:.6f},  |∇S|² = {results['H']['grad_norm_sq']:.2e}")
    print(f"  Helium:    S = {results['He']['S']:.6f},  |∇S|² = {results['He']['grad_norm_sq']:.2e}")

    if results['H']['S'] > 0:
        ratio = results['He']['S'] / results['H']['S']
        print(f"\n  S(He)/S(H) = {ratio:.4f}")
        print(f"  Expected:    ~1.86 (from Phase 1a)")

    # Check convergence
    H_converged = results['H']['grad_norm_sq'] < 1e-4
    He_converged = results['He']['grad_norm_sq'] < 1e-4
    print(f"\n  H converged:  {'✓' if H_converged else '✗'} (|∇S|² = {results['H']['grad_norm_sq']:.2e})")
    print(f"  He converged: {'✓' if He_converged else '✗'} (|∇S|² = {results['He']['grad_norm_sq']:.2e})")

    # Save results
    results_dir = os.path.join(os.path.dirname(__file__), '..', '..', 'results')
    os.makedirs(results_dir, exist_ok=True)
    outfile = os.path.join(results_dir, 'EXP_042c_Regge_JAX.txt')
    with open(outfile, 'w') as f:
        f.write("EXP_042c: Regge Stationary Points (JAX Autodiff)\n")
        f.write("=" * 50 + "\n\n")
        f.write(f"Hydrogen: S = {results['H']['S']:.6f}, |∇S|² = {results['H']['grad_norm_sq']:.2e}\n")
        f.write(f"Helium:   S = {results['He']['S']:.6f}, |∇S|² = {results['He']['grad_norm_sq']:.2e}\n")
        if results['H']['S'] > 0:
            f.write(f"S(He)/S(H) = {ratio:.4f}\n")
        f.write(f"\nH converged: {H_converged}\n")
        f.write(f"He converged: {He_converged}\n")
    print(f"\nResults saved to {outfile}")
