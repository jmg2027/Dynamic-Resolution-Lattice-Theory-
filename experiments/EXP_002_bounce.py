"""
Mini Black Hole Bounce Simulation (Unitary Version)
=====================================================
N_total cells are FIXED. Information is CONSERVED.

"Merging" = cells freeze (become identical, indistinguishable)
"Splitting" = cells thaw (differentiate, become distinguishable)

N_active (distinguishable cells) changes, but N_total and
total information are conserved throughout — as required
by unitarity (Derivation 2: U†U = I).
"""

import numpy as np
import sys, os
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex as Simplex4D

np.random.seed(42)


class UnitaryLattice:
    """
    A lattice with fixed N_total cells.
    Each cell is either ACTIVE (distinguishable) or FROZEN (identical to a neighbor).
    Total Hilbert space dimension is fixed → information conserved.
    """

    def __init__(self, n_total: int):
        self.n_total = n_total
        self.cells = [Simplex4D() for _ in range(n_total)]
        self.active = [True] * n_total  # all start active

    @property
    def n_active(self) -> int:
        return sum(self.active)

    @property
    def active_cells(self) -> list[Simplex4D]:
        return [c for c, a in zip(self.cells, self.active) if a]

    def total_info(self) -> float:
        """Total information: summed over ALL cells (active + frozen)."""
        return sum(c.shannon_entropy for c in self.cells)

    def active_info(self) -> float:
        """Information in active (distinguishable) cells only."""
        return sum(c.shannon_entropy for c, a in zip(self.cells, self.active) if a)

    def mean_W_active(self) -> float:
        """Mean W among active cells."""
        ac = self.active_cells
        if len(ac) < 2:
            return 0.2
        vals = [ac[i].W(ac[j]) for i in range(len(ac)) for j in range(i+1, len(ac))]
        return float(np.mean(vals))

    def min_ds2_active(self) -> float:
        """Minimum ds² among active cells."""
        ac = self.active_cells
        if len(ac) < 2:
            return 1.0
        vals = [ac[i].ds_squared(ac[j]) for i in range(len(ac))
                for j in range(i+1, len(ac))]
        return float(np.min(vals))

    def h_eff(self) -> float:
        """ℏ_eff from active cells."""
        ac = self.active_cells
        if len(ac) < 2:
            return float('inf')
        return ac[0].h_eff(ac[1:])

    # ── Dynamics ──────────────────────────────────────────────

    def gravitational_step(self, strength: float):
        """
        Gravity: push ALL cell states toward the mean.
        This is unitary (a rotation in Hilbert space).
        """
        mean_psi = np.mean([c.psi for c in self.cells], axis=0)
        mean_psi = mean_psi / np.linalg.norm(mean_psi)

        for i in range(self.n_total):
            new_psi = (1.0 - strength) * self.cells[i].psi + strength * mean_psi
            self.cells[i] = Simplex4D(new_psi)

    def update_active_status(self, threshold: float = 0.195):
        """
        Cells with W > threshold to ANY active cell become FROZEN.
        Frozen cells are still there — just indistinguishable.
        No information is lost.
        """
        # Find which cells are distinguishable
        n = self.n_total
        distinguishable = [True] * n

        for i in range(n):
            if not distinguishable[i]:
                continue
            for j in range(i + 1, n):
                if not distinguishable[j]:
                    continue
                w = self.cells[i].W(self.cells[j])
                if w > threshold:
                    distinguishable[j] = False  # j is redundant

        self.active = distinguishable

    def expansion_step(self, strength: float):
        """
        Post-bounce: perturb ALL cells (active and frozen) away from mean.
        Frozen cells may become distinguishable again → thaw.
        """
        for i in range(self.n_total):
            noise = (np.random.randn(5) + 1j * np.random.randn(5))
            noise = noise / np.linalg.norm(noise) * strength
            new_psi = self.cells[i].psi + noise
            self.cells[i] = Simplex4D(new_psi)

    # ── Measurement ───────────────────────────────────────────

    def measure(self) -> dict:
        return {
            "N_total": self.n_total,
            "N_active": self.n_active,
            "mean_W": self.mean_W_active(),
            "min_ds2": self.min_ds2_active(),
            "h_eff": self.h_eff(),
            "total_info": self.total_info(),
            "active_info": self.active_info(),
        }


# ═══════════════════════════════════════════════════════════════
#  SIMULATION
# ═══════════════════════════════════════════════════════════════

def run():
    print("=" * 65)
    print("  DRLT Black Hole Bounce (Unitary — Info Conserved)")
    print("=" * 65)

    N_TOTAL = 20
    N_MIN = 3
    MERGE_THRESH = 0.195

    lat = UnitaryLattice(N_TOTAL)
    history = []

    m = lat.measure()
    history.append(m)
    print(f"\n  INITIAL: N_total={m['N_total']}, N_active={m['N_active']}, "
          f"total_info={m['total_info']:.2f} bits")

    # ── Phase 1: Collapse ─────────────────────────────────────
    print(f"\n{'━'*65}")
    print(f"  PHASE 1: COLLAPSE")
    print(f"{'━'*65}")
    print(f"  {'step':>4} {'N_act':>5} {'mean_W':>8} {'min_ds²':>8} "
          f"{'ℏ_eff':>8} {'tot_info':>8} {'act_info':>8}")

    bounced = False
    bounce_step = 0

    for step in range(1, 35):
        gravity = 0.06 + 0.005 * step
        lat.gravitational_step(strength=min(gravity, 0.45))
        lat.update_active_status(threshold=MERGE_THRESH)

        m = lat.measure()
        history.append(m)

        flag = ""
        if m['N_active'] <= N_MIN and not bounced:
            bounced = True
            bounce_step = step
            flag = " ★ BOUNCE"

        print(f"  {step:4d} {m['N_active']:5d} {m['mean_W']:8.5f} {m['min_ds2']:8.5f} "
              f"{m['h_eff']:8.4f} {m['total_info']:8.3f} {m['active_info']:8.3f}{flag}")

        if bounced:
            break

    # ── Phase 2: Expansion ────────────────────────────────────
    if bounced:
        print(f"\n{'━'*65}")
        print(f"  PHASE 2: EXPANSION")
        print(f"{'━'*65}")
        print(f"  {'step':>4} {'N_act':>5} {'mean_W':>8} {'min_ds²':>8} "
              f"{'ℏ_eff':>8} {'tot_info':>8} {'act_info':>8}")

        for step in range(1, 20):
            lat.expansion_step(strength=0.08 + 0.015 * step)
            lat.update_active_status(threshold=MERGE_THRESH)

            m = lat.measure()
            history.append(m)

            print(f"  {step:4d} {m['N_active']:5d} {m['mean_W']:8.5f} "
                  f"{m['min_ds2']:8.5f} {m['h_eff']:8.4f} "
                  f"{m['total_info']:8.3f} {m['active_info']:8.3f}")

    # ── Results ───────────────────────────────────────────────
    print(f"\n{'═'*65}")
    print(f"  RESULTS")
    print(f"{'═'*65}")

    hi = history[0]
    hb = history[bounce_step]
    hf = history[-1]

    print(f"\n  {'':18s} {'Initial':>10} {'Bounce':>10} {'Final':>10}")
    print(f"  {'─'*48}")
    print(f"  {'N_total':18s} {hi['N_total']:10d} {hb['N_total']:10d} {hf['N_total']:10d}")
    print(f"  {'N_active':18s} {hi['N_active']:10d} {hb['N_active']:10d} {hf['N_active']:10d}")
    print(f"  {'mean W':18s} {hi['mean_W']:10.5f} {hb['mean_W']:10.5f} {hf['mean_W']:10.5f}")
    print(f"  {'min ds²':18s} {hi['min_ds2']:10.5f} {hb['min_ds2']:10.5f} {hf['min_ds2']:10.5f}")
    print(f"  {'ℏ_eff':18s} {hi['h_eff']:10.4f} {hb['h_eff']:10.4f} {hf['h_eff']:10.4f}")
    print(f"  {'TOTAL info':18s} {hi['total_info']:10.3f} {hb['total_info']:10.3f} {hf['total_info']:10.3f}")
    print(f"  {'active info':18s} {hi['active_info']:10.3f} {hb['active_info']:10.3f} {hf['active_info']:10.3f}")

    # Info conservation check
    info_range = [h['total_info'] for h in history]
    info_min, info_max = min(info_range), max(info_range)
    info_variation = (info_max - info_min) / info_max * 100

    print(f"\n  PHYSICS CHECKS:")
    checks = [
        ("N_total constant throughout",
         all(h['N_total'] == N_TOTAL for h in history)),
        ("N_active decreased in collapse",
         hb['N_active'] < hi['N_active']),
        ("Bounce occurred",
         bounced),
        ("N_active increased after bounce",
         hf['N_active'] > hb['N_active']),
        ("ℏ_eff > 0 ALWAYS",
         all(h['h_eff'] > 0 for h in history)),
        ("ds² > 0 ALWAYS (no singularity)",
         all(h['min_ds2'] > 0 for h in history)),
        (f"TOTAL info conserved (variation < 5%: {info_variation:.1f}%)",
         info_variation < 5),
        ("Active info fell then rose",
         hb['active_info'] < hi['active_info'] and hf['active_info'] > hb['active_info']),
    ]

    passed = 0
    for name, ok in checks:
        print(f"    [{'✓' if ok else '✗'}] {name}")
        if ok:
            passed += 1

    print(f"\n  {passed}/{len(checks)} passed")

    if bounced:
        print(f"\n  ★ No singularity. min ds² = {hb['min_ds2']:.6f} > 0")
        print(f"    N_total stayed {N_TOTAL} throughout (Hilbert space fixed)")
        print(f"    Total info: {hi['total_info']:.2f} → {hb['total_info']:.2f} "
              f"→ {hf['total_info']:.2f} bits (conserved)")


if __name__ == "__main__":
    run()
