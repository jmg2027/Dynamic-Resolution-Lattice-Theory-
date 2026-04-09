"""
Lattice: A network of Simplex4D cells forming a simplicial complex.

Curvature lives here, not in individual simplices.
A single simplex is a K₅ complete graph (10 edges, all connected).
Curvature emerges from HOW MANY simplices share each hinge,
and whether their dihedral angles sum to 2π or not.

δ_h = 2π - Σ_{simplices around hinge h} θ_k
"""

import numpy as np
from collections import defaultdict
from simplex import Simplex4D


class Lattice:
    """
    A simplicial complex: a collection of Simplex4D cells
    glued along shared faces.

    Curvature = deficit angle at each hinge (triangle).
    The number of simplices around a hinge is NOT fixed —
    it varies, and this variation IS curvature.
    """

    def __init__(self):
        self.cells: dict[int, Simplex4D] = {}
        # Adjacency: cell_id → set of neighbor cell_ids
        # Two cells are adjacent if they share a face (tetrahedron)
        self.adjacency: dict[int, set[int]] = defaultdict(set)
        # Hinges: frozenset of cell_ids that share a hinge (triangle)
        # Each hinge is identified by the set of cells around it
        self.hinges: list[list[int]] = []
        self._next_id = 0

    # ── Building the lattice ─────────────────────────────────────

    def add_cell(self, psi: np.ndarray | None = None) -> int:
        """Add a simplex cell. Returns its id."""
        cell_id = self._next_id
        self.cells[cell_id] = Simplex4D(psi)
        self._next_id += 1
        return cell_id

    def connect(self, i: int, j: int):
        """Declare cells i and j as face-adjacent (sharing a tetrahedron)."""
        self.adjacency[i].add(j)
        self.adjacency[j].add(i)

    def add_hinge(self, cell_ids: list[int]):
        """
        Register a hinge: an ordered cycle of cells sharing a triangle.

        In 4D Regge calculus, a hinge is a triangle (2-simplex).
        Multiple 4-simplices share it. The deficit angle is
        computed from the dihedral angles between consecutive
        cells in the cycle around the hinge.
        """
        self.hinges.append(cell_ids)

    # ── W matrix ─────────────────────────────────────────────────

    def W_matrix(self) -> np.ndarray:
        """
        Full W_ij matrix between all cells.

        This IS the lattice — the topology, geometry, and
        connectivity are all encoded here.
        """
        ids = sorted(self.cells.keys())
        n = len(ids)
        W = np.zeros((n, n))
        for a in range(n):
            for b in range(n):
                W[a, b] = self.cells[ids[a]].W(self.cells[ids[b]])
        return W

    # ── Curvature ────────────────────────────────────────────────

    def dihedral_angle(self, i: int, j: int) -> float:
        """θ_ij = arccos|⟨ψ_i|ψ_j⟩| between cells i and j."""
        return self.cells[i].dihedral_angle(self.cells[j])

    def deficit_angle(self, hinge_cells: list[int]) -> float:
        """
        δ = 2π - Σ θ_k  for cells around a hinge.

        The cells form a cycle around the hinge:
        θ₁₂ + θ₂₃ + ... + θₙ₁ = Σθ
        δ = 2π - Σθ

        δ > 0: positive curvature (sphere-like)
        δ = 0: flat
        δ < 0: negative curvature (saddle-like)
        """
        n = len(hinge_cells)
        if n < 2:
            return 2.0 * np.pi  # lone cell → max curvature

        theta_sum = 0.0
        for k in range(n):
            i = hinge_cells[k]
            j = hinge_cells[(k + 1) % n]
            theta_sum += self.dihedral_angle(i, j)

        return 2.0 * np.pi - theta_sum

    def all_deficit_angles(self) -> list[tuple[list[int], float]]:
        """Compute deficit angle at every registered hinge."""
        return [(h, self.deficit_angle(h)) for h in self.hinges]

    def scalar_curvature(self) -> float:
        """
        R ∝ Σ_h A_h · δ_h  (Regge curvature scalar)

        In our theory with area cancellation (D6):
        R_discrete ∝ Σ_h δ_h  (purely angular)
        """
        return sum(self.deficit_angle(h) for h in self.hinges)

    # ── Regge action (Derivation 6) ──────────────────────────────

    def regge_action_dimensionless(self) -> float:
        """
        S/ℏ = 8π·N_hinges - 4·Σ arccos|⟨ψ_i|ψ_j⟩|

        The full dimensionless action on the lattice.
        Scale-free: no lengths, no areas. (Derivation 6.3)
        """
        N_h = len(self.hinges)
        topological_term = 8.0 * np.pi * N_h

        dynamical_term = 0.0
        for h in self.hinges:
            n = len(h)
            for k in range(n):
                i, j = h[k], h[(k + 1) % n]
                dynamical_term += self.dihedral_angle(i, j)

        return topological_term - 4.0 * dynamical_term

    # ── Path integral weight (Derivation 6.5) ────────────────────

    def partition_function_weight(self) -> complex:
        """
        Z_weight = exp(i · S/ℏ)

        The path integral contribution of this lattice configuration.
        """
        return np.exp(1j * self.regge_action_dimensionless())

    # ── Analysis tools ───────────────────────────────────────────

    def curvature_summary(self) -> dict:
        """Summary statistics of the lattice curvature."""
        deficits = [self.deficit_angle(h) for h in self.hinges]
        if not deficits:
            return {"n_hinges": 0}
        return {
            "n_cells": len(self.cells),
            "n_hinges": len(self.hinges),
            "mean_deficit": float(np.mean(deficits)),
            "std_deficit": float(np.std(deficits)),
            "max_deficit": float(np.max(deficits)),
            "min_deficit": float(np.min(deficits)),
            "total_curvature": float(np.sum(deficits)),
            "action_S_over_h": self.regge_action_dimensionless(),
        }

    def W_summary(self) -> dict:
        """Summary of the W matrix (the lattice itself)."""
        W = self.W_matrix()
        n = len(self.cells)
        # Off-diagonal elements only
        mask = ~np.eye(n, dtype=bool)
        off_diag = W[mask]
        return {
            "n_cells": n,
            "W_diag": float(W[0, 0]) if n > 0 else 0,
            "W_mean": float(np.mean(off_diag)) if n > 1 else 0,
            "W_std": float(np.std(off_diag)) if n > 1 else 0,
            "W_max": float(np.max(off_diag)) if n > 1 else 0,
            "W_min": float(np.min(off_diag)) if n > 1 else 0,
        }


# ── Lattice builders ─────────────────────────────────────────────

def build_ring(n: int, angle_per_cell: float | None = None) -> Lattice:
    """
    Build a ring of n simplices sharing a common hinge.

    States are rotated in a 2D subspace of C^5 so that
    consecutive pairs have |⟨ψ_k|ψ_{k+1}⟩| = cos(angle_per_cell),
    giving dihedral angle = angle_per_cell per pair.

    If angle_per_cell = 2π/n: flat (δ = 0)
    If angle_per_cell < 2π/n: positive curvature (δ > 0)
    If angle_per_cell > 2π/n: negative curvature (δ < 0)
    """
    lat = Lattice()

    if angle_per_cell is None:
        angle_per_cell = 2.0 * np.pi / n  # flat by default

    ids = []
    for k in range(n):
        # Rotate in the (e_0, e_1) subspace → controlled overlap
        phi = k * angle_per_cell
        psi = np.array([
            np.cos(phi),
            np.sin(phi),
            0, 0, 0,
        ], dtype=complex)
        cell_id = lat.add_cell(psi)
        ids.append(cell_id)

    for k in range(n):
        lat.connect(ids[k], ids[(k + 1) % n])

    lat.add_hinge(ids)
    return lat


def build_positive_curvature(n_around: int = 4) -> Lattice:
    """Fewer cells than flat → deficit > 0 (sphere-like)."""
    # Use flat angle (2π/6) but only 4 cells → Σθ < 2π → δ > 0
    return build_ring(n_around, angle_per_cell=2 * np.pi / 6)


def build_negative_curvature(n_around: int = 8) -> Lattice:
    """More cells than flat → deficit < 0 (saddle-like)."""
    return build_ring(n_around, angle_per_cell=2 * np.pi / 6)


def build_random_lattice(n_cells: int, n_hinges: int,
                         hinge_size: int = 4) -> Lattice:
    """Build a random lattice with random states and random hinge assignments."""
    lat = Lattice()

    ids = [lat.add_cell() for _ in range(n_cells)]

    # Random hinges: pick random subsets of cells
    for _ in range(n_hinges):
        size = min(hinge_size, n_cells)
        hinge_ids = list(np.random.choice(ids, size=size, replace=False))
        lat.add_hinge(hinge_ids)
        # Connect all pairs in the hinge
        for a in hinge_ids:
            for b in hinge_ids:
                if a != b:
                    lat.connect(a, b)

    return lat


# ── Demonstrations ───────────────────────────────────────────────

if __name__ == "__main__":
    np.random.seed(42)

    print("=" * 60)
    print("DRLT Lattice — Curvature from W_ij")
    print("=" * 60)

    # 1. Flat ring: 6 cells, angle = 2π/6 each → Σθ = 2π → δ = 0
    print("\n── Flat Ring (6 cells, δ = 0) ──")
    flat = build_ring(6)  # default: angle = 2π/n → flat
    deficits = flat.all_deficit_angles()
    for cells, d in deficits:
        print(f"  δ = {d:+.6f} rad = {np.degrees(d):+.4f}°  (should be ≈ 0)")

    # 2. Positive curvature: 4 cells with same angle → gap → δ > 0
    print("\n── Positive Curvature (4 cells, same angle as flat-6) ──")
    pos = build_ring(4, angle_per_cell=2 * np.pi / 6)
    deficits = pos.all_deficit_angles()
    for cells, d in deficits:
        print(f"  δ = {d:+.4f} rad = {np.degrees(d):+.2f}°  → POSITIVE curvature")

    # 3. Negative curvature: 8 cells with same angle → excess → δ < 0
    print("\n── Negative Curvature (8 cells, same angle as flat-6) ──")
    neg = build_ring(8, angle_per_cell=2 * np.pi / 6)
    deficits = neg.all_deficit_angles()
    for cells, d in deficits:
        print(f"  δ = {d:+.4f} rad = {np.degrees(d):+.2f}°  → NEGATIVE curvature")

    # 4. Random lattice
    print("\n── Random Lattice (20 cells, 10 hinges) ──")
    rand = build_random_lattice(20, 10, hinge_size=5)
    s = rand.curvature_summary()
    print(f"  Cells: {s['n_cells']}, Hinges: {s['n_hinges']}")
    print(f"  Mean deficit angle: {s['mean_deficit']:+.4f} rad")
    print(f"  Std deficit angle:  {s['std_deficit']:.4f} rad")
    print(f"  Total curvature:    {s['total_curvature']:+.4f} rad")
    print(f"  S/ℏ = {s['action_S_over_h']:.4f}")

    # 5. W matrix analysis
    print(f"\n── W Matrix (Random Lattice) ──")
    ws = rand.W_summary()
    print(f"  W diagonal:       {ws['W_diag']:.6f}  (= 1/5 = {1/5:.6f})")
    print(f"  W off-diag mean:  {ws['W_mean']:.6f}")
    print(f"  W off-diag std:   {ws['W_std']:.6f}")
    print(f"  W range:          [{ws['W_min']:.6f}, {ws['W_max']:.6f}]")

    # 6. Key demonstration: curvature depends on valence
    print(f"\n── Curvature vs Hinge Valence ──")
    print(f"  (How many simplices share a hinge, each with θ = 60°)")
    for n in [3, 4, 5, 6, 7, 8, 9, 10]:
        lat = build_ring(n, angle_per_cell=2 * np.pi / 6)
        delta = lat.deficit_angle(list(range(n)))
        label = "FLAT" if abs(delta) < 0.01 else ("+" if delta > 0 else "−")
        bar = "█" * int(abs(np.degrees(delta)) / 5)
        print(f"  n={n:2d}: δ = {np.degrees(delta):+7.2f}°  [{label}] {bar}")

    print(f"\n{'=' * 60}")
    print("Curvature = 2π − Σθ around each hinge")
    print("Fewer cells → positive curvature (sphere)")
    print("More cells  → negative curvature (saddle)")
    print("Exact 2π    → flat (Euclidean)")
    print(f"{'=' * 60}")
