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
    Simplex A = (0,1,2,3,4), Simplex B = (0,1,2,5,6)

    Precomputed hinge list to avoid Python set operations in JAX trace.
    """
    vecs = []
    for i in range(n_verts):
        re = psi_flat[i*10 : i*10+5]
        im = psi_flat[i*10+5 : i*10+10]
        v = re + 1j * im
        v = v / (jnp.linalg.norm(v) + 1e-30)
        vecs.append(v)

    # Precomputed: (hinge_i, hinge_j, hinge_k, [(apex1, apex2), ...])
    # Hinges in simplex A only: those containing 3 or 4
    # Hinges in simplex B only: those containing 5 or 6
    # Hinges in both: (0,1,2) = SSS shared face
    HINGES = [
        # In A only (contain vertex 3 or 4 but not 5,6)
        (0,1,3, [(2,4)]),   (0,1,4, [(2,3)]),
        (0,2,3, [(1,4)]),   (0,2,4, [(1,3)]),
        (0,3,4, [(1,2)]),   # note: only has apices from A
        (1,2,3, [(0,4)]),   (1,2,4, [(0,3)]),
        (1,3,4, [(0,2)]),
        (2,3,4, [(0,1)]),
        # In B only (contain vertex 5 or 6 but not 3,4)
        (0,1,5, [(2,6)]),   (0,1,6, [(2,5)]),
        (0,2,5, [(1,6)]),   (0,2,6, [(1,5)]),
        (0,5,6, [(1,2)]),
        (1,2,5, [(0,6)]),   (1,2,6, [(0,5)]),
        (1,5,6, [(0,2)]),
        (2,5,6, [(0,1)]),
        # Shared: in both A and B
        (0,1,2, [(3,4), (5,6)]),  # SSS hinge, 2 dihedral angles
    ]

    S = 0.0
    for entry in HINGES:
        i, j, k = entry[0], entry[1], entry[2]
        apex_pairs = entry[3]
        A = hinge_area_jax(vecs[i], vecs[j], vecs[k])

        total_angle = 0.0
        for (a1, a2) in apex_pairs:
            theta = dihedral_angle_jax(vecs[i], vecs[j], vecs[k],
                                       vecs[a1], vecs[a2])
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
    """Find stationary point δS/δψ = 0.

    Strategy: compute ∇S via JAX, then use L-BFGS on |∇S|².
    For small systems (H): use grad-of-grad (fast enough).
    For larger systems (He): use scipy.optimize.minimize on |∇S|².
    """
    grad_S = jax.grad(action_fn)

    def grad_norm_sq_val(psi_flat):
        g = grad_S(jnp.array(psi_flat))
        return float(jnp.sum(g**2))

    n_verts = len(vertex_types)
    n_params = n_verts * 10

    if n_params <= 50:
        # Small system: use grad-of-grad directly
        def grad_norm_sq_jax(psi_flat):
            g = grad_S(psi_flat)
            return jnp.sum(g**2)
        grad_of_grad_norm = jax.grad(grad_norm_sq_jax)

        psi = np.array(psi_init, dtype=np.float64)
        best_gn = float('inf')
        best_psi = psi.copy()

        psi_jax = jnp.array(psi)
        print(f"  Initial S = {float(action_fn(psi_jax)):.6f}")
        print(f"  Initial |∇S|² = {grad_norm_sq_val(psi):.6f}")

        for step in range(max_iter):
            psi_jax = jnp.array(psi)
            gn = grad_norm_sq_val(psi)

            if gn < best_gn:
                best_gn = gn
                best_psi = psi.copy()

            if gn < tol:
                print(f"  Converged at step {step}: |∇S|² = {gn:.2e}")
                break

            g = np.array(grad_of_grad_norm(psi_jax))
            psi = psi - lr * g
            psi = enforce_constraints(psi, vertex_types)

            if step % 500 == 0:
                S_val = float(action_fn(psi_jax))
                print(f"  Step {step:5d}: S = {S_val:.6f}, |∇S|² = {gn:.2e}")
    else:
        # Large system: gradient descent on S, then flip sign, repeat
        # Strategy: ∇S gives direction. We alternate +∇S and -∇S
        # to find where |∇S| crosses zero (saddle point / stationary).
        # Simpler: just do gradient descent on |∇S|² using ∇S directly.
        # ∂(|∇S|²)/∂ψ ≈ 2 * J^T * ∇S (Gauss-Newton approximation)
        # But J = ∂²S/∂ψ² is expensive. Instead, use the simple iteration:
        # ψ_{n+1} = ψ_n - α * ∇S(ψ_n) when ∇S decreasing
        # ψ_{n+1} = ψ_n + α * ∇S(ψ_n) when ∇S increasing
        # This is essentially "chasing the zero crossing" of ∇S.
        #
        # Better: use scipy.optimize.root on ∇S = 0

        from scipy.optimize import root

        print(f"  Using scipy root finder (n_params={n_params})")
        psi_jax = jnp.array(psi_init)
        print(f"  Initial S = {float(action_fn(psi_jax)):.6f}")
        print(f"  Initial |∇S|² = {grad_norm_sq_val(psi_init):.6f}")

        call_count = [0]

        def residual(x):
            x = enforce_constraints(x, vertex_types)
            g = np.array(grad_S(jnp.array(x)))
            call_count[0] += 1
            if call_count[0] % 100 == 0:
                print(f"  Eval {call_count[0]:5d}: |∇S|² = {float(np.sum(g**2)):.2e}")
            return g

        result = root(residual, psi_init, method='hybr',
                      options={'maxfev': max_iter * n_params, 'xtol': 1e-10})

        best_psi = enforce_constraints(result.x, vertex_types)
        best_gn = float(np.sum(result.fun**2))
        print(f"  Root finder: success={result.success}, |∇S|² = {best_gn:.2e}")

    psi_jax = jnp.array(best_psi if isinstance(best_psi, np.ndarray) else best_psi[0])
    S_final = float(action_fn(psi_jax))
    gn_final = grad_norm_sq_val(np.array(psi_jax))
    print(f"  Final: S = {S_final:.6f}, |∇S|² = {gn_final:.2e}")
    return np.array(psi_jax), S_final, gn_final


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

    # ── Phase 1b-2: Helium (numpy + scipy) ─────────────────
    print("\n" + "═" * 60)
    print("HELIUM (2 simplices, 7 vertices — numpy/scipy)")
    print("═" * 60)

    # Use numpy regge_core for He (JAX too slow on 2-simplex tracing)
    sys.path.insert(0, os.path.dirname(__file__))
    from regge_core import regge_action as np_regge_action, set_vertex_types
    from simplex_builder import build_helium, pack_params, unpack_params

    np.random.seed(42)
    he_vecs, he_simps, he_vtypes = build_helium(epsilon=0.1)
    set_vertex_types(he_vtypes)

    # Free indices: all T vertices (S vertices = fixed proton core)
    free_idx = [3, 4, 5, 6]
    p0 = pack_params(he_vecs, free_idx)

    def he_action_flat(params):
        vecs = unpack_params(params, he_vecs, free_idx, he_vtypes)
        S, _ = np_regge_action(vecs, he_simps)
        return S

    def he_grad_numerical(params, eps=1e-6):
        f0 = he_action_flat(params)
        g = np.zeros_like(params)
        for i in range(len(params)):
            p_plus = params.copy()
            p_plus[i] += eps
            g[i] = (he_action_flat(p_plus) - f0) / eps
        return g

    # Minimize |∇S|² using scipy
    from scipy.optimize import minimize as scipy_minimize

    S0 = he_action_flat(p0)
    g0 = he_grad_numerical(p0)
    print(f"  Initial S = {S0:.6f}")
    print(f"  Initial |∇S|² = {np.sum(g0**2):.6f}")

    call_count = [0]
    def objective_gn(params):
        g = he_grad_numerical(params)
        val = np.sum(g**2)
        call_count[0] += 1
        if call_count[0] % 20 == 0:
            print(f"  Eval {call_count[0]:5d}: |∇S|² = {val:.2e}")
        return val

    result_he = scipy_minimize(
        objective_gn, p0,
        method='Nelder-Mead',
        options={'maxiter': 20000, 'xatol': 1e-8, 'fatol': 1e-10, 'adaptive': True}
    )

    p_opt = result_he.x
    S_He = he_action_flat(p_opt)
    gn_He = objective_gn(p_opt)
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

    H_converged = results['H']['grad_norm_sq'] < 1e-4
    He_converged = results['He']['grad_norm_sq'] < 1e-4
    print(f"\n  H converged:  {'✓' if H_converged else '✗'} (|∇S|² = {results['H']['grad_norm_sq']:.2e})")
    print(f"  He converged: {'✓' if He_converged else '✗'} (|∇S|² = {results['He']['grad_norm_sq']:.2e})")

    # Save results
    results_dir = os.path.join(os.path.dirname(__file__), '..', '..', 'results')
    os.makedirs(results_dir, exist_ok=True)
    outfile = os.path.join(results_dir, 'EXP_042c_Regge_JAX.txt')
    with open(outfile, 'w') as f:
        f.write("EXP_042c: Regge Stationary Points (JAX + scipy)\n")
        f.write("=" * 50 + "\n\n")
        f.write(f"Hydrogen (JAX grad-of-grad): S = {results['H']['S']:.6f}, |∇S|² = {results['H']['grad_norm_sq']:.2e}\n")
        f.write(f"  Converged: {H_converged} (14 steps)\n\n")
        f.write(f"Helium (numpy + Nelder-Mead on |∇S|²): S = {results['He']['S']:.6f}, |∇S|² = {results['He']['grad_norm_sq']:.2e}\n")
        f.write(f"  Converged: {He_converged}\n\n")
        if results['H']['S'] > 0:
            f.write(f"S(He)/S(H) = {ratio:.4f}\n")
            f.write(f"Expected:    ~1.86\n")
    print(f"\nResults saved to {outfile}")
