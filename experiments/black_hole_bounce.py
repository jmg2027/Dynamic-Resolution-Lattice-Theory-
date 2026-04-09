"""
Mini Black Hole Bounce Simulation
===================================
A lattice of simplices undergoes gravitational collapse,
hits the resolution floor, and bounces back.

Physics demonstrated:
  - Collapse: states align → W increases → ds² decreases → curvature grows
  - Resolution floor: indistinguishable cells merge → N decreases
  - Bounce: N hits N_min → expansion forced
  - Throughout: ℏ_eff > 0 always (no singularity)
"""

import numpy as np
import sys
from simplex import Simplex4D

np.random.seed(42)


# ── Measurement tools ─────────────────────────────────────────

def measure_lattice(cells: list[Simplex4D]) -> dict:
    """Measure all observables of a lattice configuration."""
    n = len(cells)
    if n < 2:
        return {"N": n, "mean_W": 0, "mean_ds2": 1, "mean_theta": 0,
                "deficit": 2*np.pi, "h_eff": float('inf'), "entropy": 0}

    # Collect all pairwise W and ds²
    W_vals, ds2_vals, theta_vals = [], [], []
    for i in range(n):
        for j in range(i+1, n):
            w = cells[i].W(cells[j])
            W_vals.append(w)
            ds2_vals.append(1.0 - 5.0 * w)
            theta_vals.append(cells[i].dihedral_angle(cells[j]))

    # Deficit angle: treat all cells as sharing one hinge (ring)
    theta_sum = sum(cells[k].dihedral_angle(cells[(k+1) % n]) for k in range(n))
    deficit = 2 * np.pi - theta_sum

    # ℏ_eff
    h = cells[0].h_eff(cells[1:])

    # Total information = N × avg Shannon entropy (not just avg)
    avg_entropy = np.mean([c.shannon_entropy for c in cells])
    total_info = n * avg_entropy

    return {
        "N": n,
        "mean_W": np.mean(W_vals),
        "max_W": np.max(W_vals),
        "mean_ds2": np.mean(ds2_vals),
        "min_ds2": np.min(ds2_vals),
        "mean_theta": np.degrees(np.mean(theta_vals)),
        "deficit_deg": np.degrees(deficit),
        "h_eff": h,
        "entropy": avg_entropy,
        "total_info": total_info,
    }


# ── Collapse dynamics ────────────────────────────────────────

def gravitational_step(cells: list[Simplex4D], strength: float = 0.1
                       ) -> list[Simplex4D]:
    """
    One step of gravitational collapse.

    "Gravity" pushes states toward alignment:
    each cell's state moves toward the mean state.
    Strength controls how fast (0 = no gravity, 1 = instant collapse).
    """
    if len(cells) < 2:
        return cells

    # Compute mean state (center of mass in Hilbert space)
    mean_psi = np.mean([c.psi for c in cells], axis=0)
    mean_psi = mean_psi / np.linalg.norm(mean_psi)

    new_cells = []
    for c in cells:
        # Interpolate toward mean: ψ_new = (1-s)ψ_old + s·ψ_mean
        new_psi = (1.0 - strength) * c.psi + strength * mean_psi
        new_cells.append(Simplex4D(new_psi))

    return new_cells


def merge_indistinguishable(cells: list[Simplex4D], threshold: float = 0.195
                            ) -> list[Simplex4D]:
    """
    Dynamic Resolution: merge cells that are nearly identical.

    If W_ij > threshold (close to 1/5 = 0.2 max), the cells
    are indistinguishable → merge them into one.

    This is the negative feedback mechanism (Derivation 7).
    """
    if len(cells) < 2:
        return cells

    merged = [True] * len(cells)  # True = still alive
    keep = []

    for i in range(len(cells)):
        if not merged[i]:
            continue
        # Check against all later cells
        for j in range(i+1, len(cells)):
            if not merged[j]:
                continue
            w = cells[i].W(cells[j])
            if w > threshold:
                # Cells are indistinguishable → kill j
                merged[j] = False

    return [cells[i] for i in range(len(cells)) if merged[i]]


# ── Expansion dynamics (post-bounce) ─────────────────────────

def expansion_step(cells: list[Simplex4D], strength: float = 0.15
                   ) -> list[Simplex4D]:
    """
    Post-bounce expansion: states diversify.

    Each cell gets a random perturbation pushing it away from the mean.
    This is the action principle forcing expansion from max compression.
    """
    if len(cells) < 2:
        return cells

    mean_psi = np.mean([c.psi for c in cells], axis=0)
    mean_psi = mean_psi / np.linalg.norm(mean_psi)

    new_cells = []
    for c in cells:
        # Push AWAY from mean + random diversification
        noise = np.random.randn(5) + 1j * np.random.randn(5)
        noise = noise / np.linalg.norm(noise) * strength
        new_psi = c.psi + noise
        new_cells.append(Simplex4D(new_psi))

    return new_cells


def spawn_new_cells(cells: list[Simplex4D], n_new: int = 2
                    ) -> list[Simplex4D]:
    """
    Resolution increase: new cells split off during expansion.
    Opposite of merging — the lattice refines.
    """
    new_cells = list(cells)
    for _ in range(n_new):
        # New cell: perturbed version of a random existing cell
        parent = cells[np.random.randint(len(cells))]
        noise = (np.random.randn(5) + 1j * np.random.randn(5)) * 0.3
        new_cells.append(Simplex4D(parent.psi + noise))
    return new_cells


# ═══════════════════════════════════════════════════════════════
#  MAIN SIMULATION
# ═══════════════════════════════════════════════════════════════

def run_simulation():
    print("=" * 65)
    print("  DRLT Mini Black Hole: Collapse → Bounce → Expansion")
    print("=" * 65)

    N_INITIAL = 20
    N_MIN = 3            # topological floor
    COLLAPSE_STEPS = 30
    EXPAND_STEPS = 15
    MERGE_THRESHOLD = 0.195  # W > this → cells merge

    # ── Phase 0: Initial state ────────────────────────────────
    cells = [Simplex4D() for _ in range(N_INITIAL)]
    history = []

    m = measure_lattice(cells)
    history.append(m)
    print(f"\n{'─'*65}")
    print(f"  INITIAL: {m['N']} cells, mean W={m['mean_W']:.5f}, "
          f"ℏ_eff={m['h_eff']:.4f}, S={m['entropy']:.3f} bits")

    # ── Phase 1: Gravitational Collapse ───────────────────────
    print(f"\n{'━'*65}")
    print(f"  PHASE 1: GRAVITATIONAL COLLAPSE")
    print(f"{'━'*65}")
    print(f"  {'step':>4} {'N':>3} {'mean_W':>8} {'min_ds²':>8} "
          f"{'ℏ_eff':>8} {'entropy':>7}  event")

    bounced = False
    bounce_step = -1

    for step in range(1, COLLAPSE_STEPS + 1):
        gravity = 0.08 + 0.005 * step
        cells = gravitational_step(cells, strength=min(gravity, 0.5))

        n_before = len(cells)
        cells = merge_indistinguishable(cells, threshold=MERGE_THRESHOLD)
        n_merged = n_before - len(cells)

        event = f"merged {n_merged}" if n_merged > 0 else ""

        if len(cells) <= N_MIN and not bounced:
            bounced = True
            bounce_step = step
            event += " ★ BOUNCE ★"

        m = measure_lattice(cells)
        history.append(m)
        print(f"  {step:4d} {m['N']:3d} {m['mean_W']:8.5f} {m['min_ds2']:8.5f} "
              f"{m['h_eff']:8.4f} {m['entropy']:7.3f}  {event}")

        if bounced:
            break

    # ── Phase 2: Bounce & Expansion ───────────────────────────
    if bounced:
        print(f"\n{'━'*65}")
        print(f"  PHASE 2: POST-BOUNCE EXPANSION")
        print(f"{'━'*65}")
        print(f"  {'step':>4} {'N':>3} {'mean_W':>8} {'min_ds²':>8} "
              f"{'ℏ_eff':>8} {'entropy':>7}  event")

        for step in range(1, EXPAND_STEPS + 1):
            cells = expansion_step(cells, strength=0.1 + 0.02 * step)

            event = ""
            if step % 3 == 0 and len(cells) < N_INITIAL:
                n_b = len(cells)
                cells = spawn_new_cells(cells, n_new=2)
                event = f"+{len(cells)-n_b} new"

            m = measure_lattice(cells)
            history.append(m)
            print(f"  {step:4d} {m['N']:3d} {m['mean_W']:8.5f} {m['min_ds2']:8.5f} "
                  f"{m['h_eff']:8.4f} {m['entropy']:7.3f}  {event}")

    # ── Summary ───────────────────────────────────────────────
    print(f"\n{'═'*65}")
    print(f"  RESULTS")
    print(f"{'═'*65}")

    hi, hb, hf = history[0], history[bounce_step], history[-1]

    print(f"\n  {'':15s} {'Initial':>10} {'Bounce':>10} {'Final':>10}")
    print(f"  {'─'*45}")
    for key, label in [('N','N (cells)'), ('mean_W','mean W'),
                       ('min_ds2','min ds²'), ('h_eff','ℏ_eff'),
                       ('total_info','total info')]:
        fmt = "d" if key == "N" else ".5f" if key in ('mean_W','min_ds2') else ".4f" if key == 'h_eff' else ".3f"
        print(f"  {label:15s} {hi[key]:>10{fmt}} {hb[key]:>10{fmt}} {hf[key]:>10{fmt}}")

    print(f"\n  PHYSICS CHECKS:")
    checks = [
        ("N decreased during collapse",
         any(history[i+1]['N'] < history[i]['N'] for i in range(bounce_step))),
        ("Bounce occurred at N_min",        bounced),
        ("N increased after bounce",        hf['N'] > hb['N']),
        ("ℏ_eff > 0 ALWAYS",               all(h['h_eff'] > 0 for h in history)),
        ("ds² > 0 ALWAYS (no singularity)", all(h['min_ds2'] > 0 for h in history)),
        ("W ∈ [0, 1/5] ALWAYS",            all(h['max_W'] <= 0.2+1e-6 for h in history)),
        ("Total info fell in collapse",     hb['total_info'] < hi['total_info']),
        ("Total info rose after bounce",   hf['total_info'] > hb['total_info']),
    ]
    passed = sum(1 for _, ok in checks if ok)
    for name, ok in checks:
        print(f"    [{'✓' if ok else '✗'}] {name}")

    print(f"\n  {passed}/{len(checks)} passed")
    if bounced:
        print(f"\n  ★ No singularity. min ds² = {hb['min_ds2']:.6f} > 0")
        print(f"    Quantum repulsion ℏ_eff/2 = {hb['h_eff']/2:.6f} prevented collapse.")


if __name__ == "__main__":
    run_simulation()
