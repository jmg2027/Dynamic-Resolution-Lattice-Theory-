"""
DRLT Full Pipeline Demo
========================
simplex → ψ → W_ij → g_μν(10 edges) → hinge deformation → curvature

Each stage is demonstrated and verified against analytic predictions.
"""

import numpy as np
from simplex import Simplex4D

np.random.seed(42)


def banner(title):
    print(f"\n{'='*60}")
    print(f"  {title}")
    print(f"{'='*60}")


# ═══════════════════════════════════════════════════════════════
#  STAGE 1: Simplex Structure & Wavefunction
# ═══════════════════════════════════════════════════════════════

def stage1_simplex_and_psi():
    """
    A 4-simplex is a cell of spacetime with 5 vertices.
    Each vertex is a "register" holding one component of |ψ⟩ ∈ C^5.

    The (2,3) causal split:
      vertices 0,1 → temporal (SU(2) sector)
      vertices 2,3,4 → spatial (SU(3) sector)

    The state |ψ⟩ = Σ c_k |e_k⟩ is normalized: Σ|c_k|² = 1
    """
    banner("STAGE 1: Simplex & Wavefunction |ψ⟩")

    # Create a simplex with a specific state
    psi = np.array([0.5+0.1j, 0.3-0.2j, 0.4+0.3j, 0.2-0.1j, 0.1+0.4j])
    cell = Simplex4D(psi)

    print("\n[Structure]")
    print(f"  Dimension d = {cell.D}")
    print(f"  Vertices    = {cell.N_VERTICES}  (= d+1)")
    print(f"  Edges       = {cell.N_EDGES}  (= C(5,2))")
    print(f"  Temporal vertices: {cell.TEMPORAL_VERTICES}  → SU(2)")
    print(f"  Spatial vertices:  {cell.SPATIAL_VERTICES}  → SU(3)")

    print("\n[Wavefunction |ψ⟩]")
    for k in range(5):
        label = "T" if k < 2 else "S"
        c = cell.psi[k]
        print(f"  c_{k} = {c:.4f}  |c_{k}|² = {abs(c)**2:.4f}  [{label}]")

    print(f"\n[Normalization check]")
    norm = np.sum(np.abs(cell.psi)**2)
    print(f"  ⟨ψ|ψ⟩ = {norm:.10f}  (forced to 1 by axiom)")

    print(f"\n[Information content]")
    print(f"  Shannon entropy = {cell.shannon_entropy:.4f} bits")
    print(f"  Maximum possible = {np.log2(5):.4f} bits (= log₂5)")

    print(f"\n[Causal (2,3) split]")
    print(f"  Temporal weight |SU(2)| = {cell.temporal_weight:.4f}")
    print(f"  Spatial weight  |SU(3)| = {cell.spatial_weight:.4f}")
    print(f"  Sum = {cell.temporal_weight + cell.spatial_weight:.4f}")

    return cell


# ═══════════════════════════════════════════════════════════════
#  STAGE 2: ψ → W_ij (The Axiom)
# ═══════════════════════════════════════════════════════════════

def stage2_W_matrix(cells: list[Simplex4D]):
    """
    W_ij = |⟨ψ_i|ψ_j⟩|² / (d+1)

    This is the ONLY formula in the axiom. Everything else derives from it.

    Properties to verify:
      W_ii = 1/(d+1) = 0.2    (normalization)
      W_ij = W_ji              (symmetric)
      0 ≤ W_ij ≤ 1/(d+1)      (bounded)
    """
    banner("STAGE 2: ψ → W_ij (The Axiom)")

    n = len(cells)
    W = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            W[i, j] = cells[i].W(cells[j])

    print(f"\n[W matrix ({n}×{n})]")
    header = "      " + "".join(f"   cell_{j}" for j in range(n))
    print(header)
    for i in range(n):
        row = f"  c_{i}: " + "  ".join(f"{W[i,j]:.5f}" for j in range(n))
        print(row)

    # Verify axiom properties
    print(f"\n[Verification]")
    diag_ok = all(abs(W[i, i] - 0.2) < 1e-10 for i in range(n))
    print(f"  W_ii = 1/5 = 0.2 for all i:  {'✓' if diag_ok else '✗'}")

    sym_ok = np.allclose(W, W.T)
    print(f"  W_ij = W_ji (symmetric):      {'✓' if sym_ok else '✗'}")

    bounded = np.all(W >= -1e-10) and np.all(W <= 0.2 + 1e-10)
    print(f"  0 ≤ W_ij ≤ 1/5:              {'✓' if bounded else '✗'}")

    # Sum rule (completeness)
    print(f"\n[Sum rule: Σ_j W_ij when neighbors form a basis]")
    if n >= 5:
        row_sums = np.sum(W, axis=1)
        for i in range(n):
            print(f"  Σ_j W_{i}j = {row_sums[i]:.5f}")

    return W


# ═══════════════════════════════════════════════════════════════
#  STAGE 3: W_ij → g_μν (10 edges = metric tensor)
# ═══════════════════════════════════════════════════════════════

def stage3_metric_tensor(cells: list[Simplex4D], W: np.ndarray):
    """
    The 10 inter-cell W values map to the 10 components of g_μν.

    ds²_ij = 1 - (d+1)·W_ij   (emergent metric)
    θ_ij   = arccos√(5·W_ij)   (dihedral angle)

    Also: each edge carries TWO channels:
      |⟨ψ_i|ψ_j⟩|² → metric (magnitude) → gravity
      arg⟨ψ_i|ψ_j⟩  → connection (phase)  → gauge field
    """
    banner("STAGE 3: W_ij → Metric & Gauge")

    n = len(cells)
    print(f"\n[Emergent metric: ds²_ij = 1 - 5·W_ij]")
    print(f"{'pair':>8}  {'W_ij':>8}  {'ds²':>8}  {'θ (deg)':>8}  {'phase':>8}  interpretation")
    print(f"  {'─'*70}")

    for i in range(n):
        for j in range(i + 1, n):
            w = W[i, j]
            ds2 = 1.0 - 5.0 * w
            theta = cells[i].dihedral_angle(cells[j])
            phase = np.angle(cells[i].overlap(cells[j]))

            if ds2 > 0.99:
                interp = "← far (nearly orthogonal)"
            elif ds2 < 0.01:
                interp = "← close (nearly identical)"
            else:
                interp = ""

            print(f"  ({i},{j})  {w:8.5f}  {ds2:8.5f}  {np.degrees(theta):8.2f}°"
                  f"  {phase:+8.4f}  {interp}")

    # Verify: ds² > 0 for all distinct pairs (singularity impossible)
    print(f"\n[Singularity check: ds² > 0 for all distinct pairs]")
    all_positive = True
    for i in range(n):
        for j in range(i + 1, n):
            ds2 = 1.0 - 5.0 * W[i, j]
            if ds2 <= 0:
                all_positive = False
                print(f"  WARNING: ds²({i},{j}) = {ds2:.6f} ≤ 0!")
    if all_positive:
        print(f"  All ds² > 0 ✓  (zero distance forbidden, Derivation 7)")


# ═══════════════════════════════════════════════════════════════
#  STAGE 4: Metric → Hinge Deformation → Curvature
# ═══════════════════════════════════════════════════════════════

def stage4_curvature(cells: list[Simplex4D]):
    """
    Curvature = deficit angle at a hinge (triangle).

    A hinge is shared by multiple simplices. The dihedral angles
    of all simplices around the hinge sum to Σθ.
    δ = 2π - Σθ

    Three configurations:
      Flat:     Σθ = 2π → δ = 0
      Positive: Σθ < 2π → δ > 0  (sphere-like)
      Negative: Σθ > 2π → δ < 0  (saddle-like)
    """
    banner("STAGE 4: Hinge Deformation → Curvature")

    print("\n[How curvature works]")
    print("  Each hinge (triangle) is surrounded by N simplices.")
    print("  Each simplex contributes a dihedral angle θ_k.")
    print("  Deficit angle: δ = 2π - Σ θ_k")

    alpha = np.pi / 3  # 60° per pair

    # In a ring of n cells, each rotated by α, consecutive overlap = cos(α).
    # But the LAST→FIRST pair wraps around: overlap = cos(n*α mod 2π).
    # For flat: n*α = 2π → wrap = cos(0) = 1 → θ_wrap = 0 → Σθ = (n-1)*α + 0 = 2π - α
    # Wait, let's just compute and compare.
    configs = [
        ("Flat (6 cells)",     6, alpha),
        ("Positive (4 cells)", 4, alpha),
        ("Negative (8 cells)", 8, alpha),
    ]

    results = []
    for name, n, angle in configs:
        ring_cells = []
        for k in range(n):
            phi = k * angle
            psi = np.array([np.cos(phi), np.sin(phi), 0, 0, 0], dtype=complex)
            ring_cells.append(Simplex4D(psi))

        thetas = []
        for k in range(n):
            th = ring_cells[k].dihedral_angle(ring_cells[(k + 1) % n])
            thetas.append(th)

        sum_theta = sum(thetas)
        delta = 2 * np.pi - sum_theta

        if abs(delta) < 1e-6:
            curv_type = "FLAT"
        elif delta > 0:
            curv_type = "POSITIVE (sphere-like)"
        else:
            curv_type = "NEGATIVE (saddle-like)"

        print(f"\n  [{name}]")
        print(f"    N cells around hinge: {n}")
        print(f"    Angles: {', '.join(f'{np.degrees(t):.1f}°' for t in thetas)}")
        print(f"    Σθ = {np.degrees(sum_theta):.1f}°")
        print(f"    δ  = 2π − Σθ = {np.degrees(delta):+.1f}°  → {curv_type}")
        results.append((name, delta))

    # Gram determinant → hinge area
    print(f"\n[Hinge area from Gram determinant]")
    if len(cells) >= 3:
        area = Simplex4D.hinge_area(cells[:3])
        phi_h = cells[0].holonomy_phase(cells[1], cells[2])
        print(f"  A_h = √det(G) = {area:.6f}")
        print(f"  Holonomy Φ = {np.degrees(phi_h):.2f}° (discrete Wilson loop)")

    return results


# ═══════════════════════════════════════════════════════════════
#  STAGE 5: Regge Action & ℏ_eff
# ═══════════════════════════════════════════════════════════════

def stage5_action_and_hbar(cells: list[Simplex4D]):
    """
    The Regge action with area cancellation (Derivation 6):
      S/ℏ = 4·δ  per hinge  (area drops out!)

    ℏ_eff = A·c³/(4G·S_info)  (Derivation 12)
    """
    banner("STAGE 5: Action (Area Cancels!) & ℏ_eff")

    # Show area cancellation
    print("\n[Area cancellation demonstration]")
    print("  Regge action per hinge: S_h = A_h · δ_h")
    print("  Local ℏ per hinge:      ℏ_h = A_h · c³/(4G)")
    print("  Ratio: S_h/ℏ_h = A_h·δ_h / (A_h·c³/4G) = (4G/c³)·δ_h")
    print("  → A_h CANCELS. Action is purely angular.")

    # Compute for cell pairs
    print(f"\n[Action contributions (G=c=1)]")
    for i in range(len(cells)):
        for j in range(i+1, min(i+3, len(cells))):
            theta = cells[i].dihedral_angle(cells[j])
            w_ij = cells[i].W(cells[j])
            # For a single pair, "deficit" is 2π - θ
            delta = 2*np.pi - theta
            action = 4.0 * delta
            print(f"  pair({i},{j}): θ={np.degrees(theta):6.1f}°  "
                  f"δ=2π−θ={np.degrees(delta):+7.1f}°  S/ℏ=4δ={action:.3f}")

    # ℏ_eff
    print(f"\n[ℏ_eff computation (Derivation 12)]")
    if len(cells) >= 2:
        h = cells[0].h_eff(cells[1:])
        print(f"  ℏ_eff = A·c³/(4G·S_info) = {h:.6f}")
        print(f"  ℏ_eff/2 = {h/2:.6f}  (minimum ΔxΔp — quantum repulsion)")
        print(f"  ℏ_eff > 0: {h > 0}  → singularity impossible")


# ═══════════════════════════════════════════════════════════════
#  STAGE 6: Full Pipeline Summary
# ═══════════════════════════════════════════════════════════════

def stage6_summary():
    banner("PIPELINE SUMMARY")
    print("""
    ψ ∈ C^5          5 complex registers at vertices
        │
        ▼
    W_ij = |⟨ψ_i|ψ_j⟩|²/5     THE AXIOM (one formula)
        │
        ├──magnitude──→  ds² = 1-5W  ──→  g_μν (10 components)
        │                                      │
        └──phase──────→  arg⟨i|j⟩   ──→  gauge connection
                                               │
                              ┌─────────────────┘
                              ▼
                    hinge: N simplices share a triangle
                              │
                              ▼
                    δ = 2π - Σθ_k   (deficit angle = curvature)
                              │
                              ▼
                    S/ℏ = 4·Σδ      (action — area cancelled!)
                              │
                              ▼
                    ℏ_eff = A·c³/(4G·S_info)   (computable!)
                              │
                              ▼
                    ΔxΔp ≥ ℏ_eff/2 > 0         (no singularity)
    """)


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    banner("DRLT FULL PIPELINE: ψ → W → g_μν → curvature")

    # Stage 1: Create 5 simplices with different states
    cell_a = stage1_simplex_and_psi()

    # Create a few more cells for the lattice
    cells = [cell_a]
    states = [
        np.array([0.1+0.3j, 0.5-0.1j, 0.2+0.2j, 0.3-0.3j, 0.4+0.1j]),
        np.array([0.3-0.2j, 0.1+0.4j, 0.5+0.1j, 0.1-0.2j, 0.2+0.3j]),
        np.array([0.4+0.2j, 0.2-0.3j, 0.1+0.1j, 0.5-0.1j, 0.3+0.4j]),
        np.array([0.2+0.1j, 0.4+0.2j, 0.3-0.1j, 0.2+0.4j, 0.5-0.2j]),
    ]
    for s in states:
        cells.append(Simplex4D(s))

    # Stage 2: W matrix
    W = stage2_W_matrix(cells)

    # Stage 3: Metric tensor
    stage3_metric_tensor(cells, W)

    # Stage 4: Curvature
    curv_results = stage4_curvature(cells)

    # Stage 5: Action & ℏ
    stage5_action_and_hbar(cells)

    # Stage 6: Summary
    stage6_summary()

    # Final verification count
    banner("VERIFICATION SCORECARD")
    checks = [
        ("W_ii = 1/5",            all(abs(W[i,i]-0.2) < 1e-10 for i in range(5))),
        ("W_ij = W_ji",           np.allclose(W, W.T)),
        ("0 ≤ W ≤ 1/5",          np.all(W >= -1e-10) and np.all(W <= 0.2+1e-10)),
        ("ds² > 0 (distinct)",    all(1-5*W[i,j] > 0 for i in range(5) for j in range(5) if i != j)),
        ("Flat: δ = 0",             abs(curv_results[0][1]) < 1e-6),
        ("Positive: δ > 0",        curv_results[1][1] > 0),
        ("Negative: δ < 0",        curv_results[2][1] < 0),
        ("ℏ_eff > 0",             cells[0].h_eff(cells[1:]) > 0),
        ("temporal+spatial = 1",  abs(cell_a.temporal_weight + cell_a.spatial_weight - 1) < 1e-10),
    ]

    passed = 0
    for name, ok in checks:
        status = "✓ PASS" if ok else "✗ FAIL"
        print(f"  [{status}]  {name}")
        if ok:
            passed += 1

    print(f"\n  Result: {passed}/{len(checks)} checks passed")
    print(f"  All from ONE axiom: W_ij = |⟨ψ_i|ψ_j⟩|²/(d+1)")
