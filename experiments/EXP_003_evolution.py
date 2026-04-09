"""
DRLT Time Evolution
====================
Watch the vertex network evolve:
  ψ values change → W pattern shifts → simplices form/dissolve →
  curvature changes → spacetime restructures

The 4-simplex already contains time, so "evolution" here means
scanning through different ψ configurations — like slicing
through a block universe.
"""

import numpy as np
import sys, os
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network, make_clustered_network

np.random.seed(42)


def _expm_hermitian(H: np.ndarray, dt: float) -> np.ndarray:
    """e^{-iHdt} for Hermitian H via eigendecomposition."""
    eigvals, eigvecs = np.linalg.eigh(H)
    return eigvecs @ np.diag(np.exp(-1j * eigvals * dt)) @ eigvecs.conj().T


def local_unitary_step(net: Network, mode: str = "gravity", dt: float = 0.1):
    """
    LOCAL unitary evolution: each vertex gets a DIFFERENT Hamiltonian
    that depends on its neighbors' states.

    A global U doesn't change W (gauge invariance).
    Only LOCAL (vertex-dependent) evolution changes the physics.
    """
    n = net.N
    new_psis = []

    for i in range(n):
        # Build LOCAL Hamiltonian for vertex i from its interactions
        H_i = _local_hamiltonian(net, i, mode)
        U_i = _expm_hermitian(H_i, dt)
        new_psis.append(U_i @ net.vertices[i].psi)

    for i in range(n):
        net.vertices[i] = Vertex(new_psis[i])


def _local_hamiltonian(net: Network, i: int, mode: str) -> np.ndarray:
    """
    Vertex i's Hamiltonian depends on its W_ij with all others.

    'gravity':  H_i pulls ψ_i toward its neighbors (W-weighted mean)
    'expand':   H_i pushes ψ_i away from neighbors
    'free':     H_i = random perturbation unique to each vertex
    """
    psi_i = net.vertices[i].psi
    n = net.N

    if mode == "gravity":
        # Interaction: attract toward W-weighted mean of neighbors
        mean_neighbor = np.zeros(5, dtype=complex)
        for j in range(n):
            if j == i:
                continue
            w = net.vertices[i].W(net.vertices[j])
            mean_neighbor += w * net.vertices[j].psi
        if np.linalg.norm(mean_neighbor) > 1e-15:
            mean_neighbor /= np.linalg.norm(mean_neighbor)
        # H = |mean⟩⟨mean| projects toward the mean → attraction
        H = np.outer(mean_neighbor, mean_neighbor.conj())

    elif mode == "expand":
        # Interaction: each vertex rotates at a rate proportional to index
        # Different rates → states diverge
        H = np.diag(np.arange(5, dtype=float) * (i + 1) / n)

    elif mode == "free":
        # Small random Hermitian unique to this vertex
        np.random.seed(i * 1000 + int(np.abs(psi_i[0]) * 1e6) % 1000)
        A = np.random.randn(5, 5) + 1j * np.random.randn(5, 5)
        H = (A + A.conj().T) / 2 * 0.3

    else:
        H = np.zeros((5, 5), dtype=complex)

    return H


def snapshot(net: Network, w_thresh: float = 0.03) -> dict:
    """Measure everything at one instant."""
    simplices = net.find_simplices(w_threshold=w_thresh)
    faces = net.find_shared_faces(simplices) if simplices else []
    curv = net.curvature_map(simplices) if simplices else []

    deficits = [d for _, d, _ in curv] if curv else [0.0]

    return {
        "N_vert": net.N,
        "N_simp": len(simplices),
        "N_faces": len(faces),
        "N_hinges": len(curv),
        "mean_W": net.mean_W(),
        "min_ds2": net.min_ds2(),
        "total_info": net.total_info(),
        "mean_curv": float(np.mean(deficits)) if curv else 0.0,
    }


# ═══════════════════════════════════════════════════════════════

def run():
    W_THRESH = 0.03

    print("=" * 70)
    print("  DRLT Evolution: Watch Spacetime Form, Collapse, and Restructure")
    print("=" * 70)

    # ── Build initial network ────────────────────────────────
    net = make_clustered_network(n_clusters=3, per_cluster=5, spread=0.35)
    print(f"\n  {net.N} vertices in 3 clusters")

    header = (f"  {'t':>4} {'simp':>5} {'faces':>5} {'hinges':>6} "
              f"{'mean_W':>8} {'min_ds²':>8} {'info':>7} {'curv°':>7}  phase")
    sep = f"  {'─'*65}"

    history = []

    def log(t, phase_name=""):
        s = snapshot(net, w_thresh=W_THRESH)
        s['t'] = t
        history.append(s)
        print(f"  {t:4d} {s['N_simp']:5d} {s['N_faces']:5d} {s['N_hinges']:6d} "
              f"{s['mean_W']:8.5f} {s['min_ds2']:8.5f} "
              f"{s['total_info']:7.2f} {np.degrees(s['mean_curv']):+7.1f}  {phase_name}")

    # ── Phase 1: Free evolution (spacetime forms) ─────────────
    print(f"\n{'━'*70}")
    print(f"  PHASE 1: FREE EVOLUTION — spacetime crystallizes")
    print(f"{'━'*70}")
    print(header)
    print(sep)

    log(0, "initial")
    for t in range(1, 11):
        local_unitary_step(net, mode="free", dt=0.15)
        log(t)

    # ── Phase 2: Gravitational collapse ──────────────────────
    print(f"\n{'━'*70}")
    print(f"  PHASE 2: GRAVITY ON — collapse, simplices merge")
    print(f"{'━'*70}")
    print(header)
    print(sep)

    for t in range(11, 26):
        local_unitary_step(net, mode="gravity", dt=0.2)
        log(t, "gravity" if t == 11 else "")

    # ── Phase 3: Expansion ───────────────────────────────────
    print(f"\n{'━'*70}")
    print(f"  PHASE 3: EXPANSION — spacetime diversifies")
    print(f"{'━'*70}")
    print(header)
    print(sep)

    for t in range(26, 41):
        local_unitary_step(net, mode="expand", dt=0.2)
        log(t, "expand" if t == 26 else "")

    # ── Summary ──────────────────────────────────────────────
    print(f"\n{'═'*70}")
    print(f"  SUMMARY")
    print(f"{'═'*70}")

    h0 = history[0]
    h_mid = history[25]   # end of collapse
    h_end = history[-1]

    print(f"\n  {'':15s} {'t=0':>10} {'t=25':>10} {'t=40':>10}")
    print(f"  {'─'*45}")
    print(f"  {'simplices':15s} {h0['N_simp']:10d} {h_mid['N_simp']:10d} {h_end['N_simp']:10d}")
    print(f"  {'faces':15s} {h0['N_faces']:10d} {h_mid['N_faces']:10d} {h_end['N_faces']:10d}")
    print(f"  {'mean W':15s} {h0['mean_W']:10.5f} {h_mid['mean_W']:10.5f} {h_end['mean_W']:10.5f}")
    print(f"  {'min ds²':15s} {h0['min_ds2']:10.5f} {h_mid['min_ds2']:10.5f} {h_end['min_ds2']:10.5f}")
    print(f"  {'total info':15s} {h0['total_info']:10.2f} {h_mid['total_info']:10.2f} {h_end['total_info']:10.2f}")

    # Information conservation check
    infos = [h['total_info'] for h in history]
    info_var = (max(infos) - min(infos)) / max(infos) * 100
    ds2s = [h['min_ds2'] for h in history]

    print(f"\n  CHECKS:")
    print(f"    [{'✓' if all(d > 0 for d in ds2s) else '✗'}] "
          f"ds² > 0 always (no singularity)")
    print(f"    [{'✓' if info_var < 1 else '✗'}] "
          f"info conserved (variation: {info_var:.2f}%)")
    print(f"    [{'✓' if h_mid['N_simp'] != h0['N_simp'] else '~'}] "
          f"simplex count changed (spacetime restructured)")

    # Show the movie in compact form
    print(f"\n  TIMELINE (simplex count):")
    max_s = max(h['N_simp'] for h in history)
    for h in history:
        bar_len = int(h['N_simp'] / max(max_s, 1) * 40)
        bar = "█" * bar_len
        print(f"    t={h['t']:3d} │{bar:<40s}│ {h['N_simp']:3d} simplices")


if __name__ == "__main__":
    run()
