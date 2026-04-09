"""
CMB Power Spectrum from DRLT
=============================
During inflation, each vertex's local W fluctuates.
These fluctuations = primordial density perturbations.
Their power spectrum P(k) ∝ k^(n_s - 1) gives the spectral index n_s.

Planck 2018 measured: n_s = 0.9649 ± 0.0042

Can we get this from the axiom?
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network, big_bounce_initial, evolve_step, try_pachner_1to5, try_pachner_5to1

np.random.seed(42)


def local_W(net: Network, i: int) -> float:
    """
    Local "density" at vertex i = mean W with all neighbors.
    High local W = dense region. Low = void.
    """
    n = net.N
    if n < 2:
        return 0.2
    return float(np.mean([net.vertices[i].W(net.vertices[j])
                          for j in range(n) if j != i]))


def W_fluctuation_field(net: Network) -> np.ndarray:
    """
    δW_i = W_i - ⟨W⟩  (density contrast at each vertex)
    """
    n = net.N
    local_Ws = np.array([local_W(net, i) for i in range(n)])
    mean_W = np.mean(local_Ws)
    return local_Ws - mean_W, local_Ws, mean_W


def power_spectrum(delta_W: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """
    P(k) = |FT(δW)|²
    On a 1D array of vertices (we treat vertex index as position).
    """
    n = len(delta_W)
    ft = np.fft.rfft(delta_W)
    pk = np.abs(ft) ** 2 / n
    k = np.fft.rfftfreq(n, d=1.0) * 2 * np.pi  # wavenumber
    return k[1:], pk[1:]  # skip k=0 (mean)


def fit_spectral_index(k: np.ndarray, pk: np.ndarray) -> float:
    """
    Fit P(k) ∝ k^(n_s - 1) → log P = (n_s-1) log k + const
    Returns n_s.
    """
    mask = (k > 0) & (pk > 1e-20)
    if np.sum(mask) < 3:
        return 1.0
    log_k = np.log(k[mask])
    log_pk = np.log(pk[mask])
    coeffs = np.polyfit(log_k, log_pk, 1)
    return coeffs[0] + 1  # slope = n_s - 1 → n_s = slope + 1


# ═══════════════════════════════════════════════════════════════

def run():
    print("=" * 70)
    print("  DRLT → CMB Power Spectrum")
    print("=" * 70)

    # Run universe until inflation happens
    net = big_bounce_initial(n_vertices=6)
    N_TARGET = 35  # want enough vertices for meaningful spectrum

    print(f"\n  Evolving until N ≥ {N_TARGET}...")

    snapshots = []  # (t, delta_W, N)
    t = 0
    while net.N < N_TARGET and t < 500:
        evolve_step(net, dt=0.08)
        try_pachner_1to5(net)
        try_pachner_5to1(net)

        if t % 10 == 0 and net.N >= 8:
            dW, Ws, mean = W_fluctuation_field(net)
            snapshots.append((t, net.N, dW.copy(), Ws.copy(), mean))

        if t % 50 == 0:
            print(f"    t={t:4d}  N={net.N:3d}")
        t += 1

    print(f"  Reached N={net.N} at t={t}")

    # Continue evolving post-inflation for structure formation
    print(f"\n  Post-inflation evolution (200 more steps)...")
    for dt_extra in range(200):
        evolve_step(net, dt=0.08)
        if (t + dt_extra) % 10 == 0:
            dW, Ws, mean = W_fluctuation_field(net)
            snapshots.append((t + dt_extra, net.N, dW.copy(), Ws.copy(), mean))
    t += 200

    # ── Analyze power spectrum at key moments ─────────────────
    print(f"\n{'━'*70}")
    print(f"  DENSITY FLUCTUATIONS & POWER SPECTRUM")
    print(f"{'━'*70}")

    ns_values = []
    for snap_t, snap_N, dW, Ws, mean_W in snapshots:
        if snap_N < 10:
            continue
        k, pk = power_spectrum(dW)
        if len(k) < 3:
            continue
        ns = fit_spectral_index(k, pk)
        variance = float(np.var(dW))
        ns_values.append((snap_t, snap_N, ns, variance, mean_W))

    print(f"\n  {'t':>4} {'N':>4} {'n_s':>8} {'σ²(δW)':>12} {'⟨W⟩':>8}  interpretation")
    print(f"  {'─'*60}")
    for snap_t, snap_N, ns, var, mW in ns_values[::max(1, len(ns_values)//20)]:
        if snap_N < 15:
            interp = "pre-inflation"
        elif var < 1e-5:
            interp = "smooth (inflation)"
        else:
            interp = "structure forming"
        print(f"  {snap_t:4d} {snap_N:4d} {ns:8.4f} {var:12.2e} {mW:8.5f}  {interp}")

    # ── Spectral index summary ────────────────────────────────
    if ns_values:
        # Use post-inflation values (after N stabilizes)
        post_inflation = [(t, N, ns, v, mW) for t, N, ns, v, mW in ns_values
                          if N >= N_TARGET - 5]
        if post_inflation:
            ns_array = np.array([ns for _, _, ns, _, _ in post_inflation])
            ns_mean = np.mean(ns_array)
            ns_std = np.std(ns_array)

            print(f"\n{'━'*70}")
            print(f"  SPECTRAL INDEX MEASUREMENT")
            print(f"{'━'*70}")
            print(f"\n  n_s (DRLT) = {ns_mean:.4f} ± {ns_std:.4f}")
            print(f"  n_s (Planck 2018) = 0.9649 ± 0.0042")
            print(f"")
            if abs(ns_mean - 0.9649) < 3 * max(ns_std, 0.05):
                print(f"  Within reasonable range ✓")
            else:
                print(f"  Discrepancy: Δn_s = {ns_mean - 0.9649:+.4f}")
                print(f"  (Expected: small N lattice gives different n_s)")
            print(f"  n_s < 1: {'✓ red-tilted (like CMB)' if ns_mean < 1 else '✗ blue-tilted'}")

    # ── Structure formation ───────────────────────────────────
    print(f"\n{'━'*70}")
    print(f"  POST-INFLATION STRUCTURE")
    print(f"{'━'*70}")

    dW_final, Ws_final, mean_final = W_fluctuation_field(net)
    print(f"\n  Final W field ({net.N} vertices):")
    print(f"  Mean W = {mean_final:.5f}")
    print(f"  σ(δW) = {np.std(dW_final):.6f}")
    print(f"")

    # Identify clusters (high W) and voids (low W)
    sorted_idx = np.argsort(Ws_final)
    n = len(sorted_idx)
    n_show = min(5, n // 4)

    print(f"  Densest vertices (future 'galaxies'):")
    for i in sorted_idx[-n_show:]:
        print(f"    vertex {i}: W_local = {Ws_final[i]:.5f} "
              f"(+{(Ws_final[i]-mean_final)/mean_final*100:.1f}% above mean)")

    print(f"\n  Emptiest vertices ('voids'):")
    for i in sorted_idx[:n_show]:
        print(f"    vertex {i}: W_local = {Ws_final[i]:.5f} "
              f"({(Ws_final[i]-mean_final)/mean_final*100:.1f}% below mean)")

    contrast = (Ws_final.max() - Ws_final.min()) / mean_final
    print(f"\n  Density contrast: {contrast:.4f}")
    print(f"  (This seeds large-scale structure formation)")


if __name__ == "__main__":
    run()
