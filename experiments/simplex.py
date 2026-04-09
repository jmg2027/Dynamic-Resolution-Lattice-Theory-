"""
Simplex4D: A single 4-simplex cell of Dynamic Resolution Lattice Theory.

Axiom: Each simplex cell is assigned |ψ⟩ ∈ C^(d+1),
       W_ij = |⟨ψ_i|ψ_j⟩|² / (d+1)

This class implements one simplex with d=4 (spacetime dimension),
encoding all derived quantities from the axiom.
"""

import numpy as np
from itertools import combinations


class Simplex4D:
    """A single 4-simplex: 5 vertices, 10 edges, state in C^5."""

    D = 4            # spacetime dimension
    N_VERTICES = 5   # d + 1
    N_EDGES = 10     # C(5,2)

    # Causal structure: (2,3) split — 2 temporal, 3 spatial
    TEMPORAL_VERTICES = [0, 1]
    SPATIAL_VERTICES = [2, 3, 4]

    # All 10 edge pairs
    EDGES = list(combinations(range(5), 2))

    def __init__(self, psi: np.ndarray | None = None):
        """
        Initialize a 4-simplex with a quantum state.

        Args:
            psi: State vector in C^5 (will be normalized).
                 If None, a random state on CP^4 is generated.
        """
        if psi is None:
            psi = self._random_state()
        self.psi = self._normalize(psi.astype(np.complex128))

    # ── State management ──────────────────────────────────────────

    @staticmethod
    def _normalize(psi: np.ndarray) -> np.ndarray:
        """Normalize to ⟨ψ|ψ⟩ = 1. (Derivation 1: forced by W_ii consistency.)"""
        norm = np.linalg.norm(psi)
        if norm < 1e-15:
            raise ValueError("Cannot normalize zero vector")
        return psi / norm

    @staticmethod
    def _random_state() -> np.ndarray:
        """Random state on CP^4 (Haar-uniform on S^9 ⊂ C^5)."""
        real = np.random.randn(5)
        imag = np.random.randn(5)
        return real + 1j * imag

    @property
    def probabilities(self) -> np.ndarray:
        """p_k = |c_k|² — probability simplex Δ^d. (Derivation 1.4)"""
        return np.abs(self.psi) ** 2

    @property
    def phases(self) -> np.ndarray:
        """φ_k = arg(c_k) — relative phases. (Derivation 1.4)"""
        return np.angle(self.psi)

    @property
    def shannon_entropy(self) -> float:
        """S = -Σ p_k log₂ p_k — information content. (Derivation 3)"""
        p = self.probabilities
        p = p[p > 1e-15]  # avoid log(0)
        return -np.sum(p * np.log2(p))

    # ── W_ij: the core of the axiom ──────────────────────────────

    def W(self, other: "Simplex4D") -> float:
        """
        W_ij = |⟨ψ_i|ψ_j⟩|² / (d+1)

        The fundamental weight between two simplex cells.
        """
        overlap = np.vdot(self.psi, other.psi)  # ⟨ψ_i|ψ_j⟩
        return float(np.abs(overlap) ** 2) / self.N_VERTICES

    def overlap(self, other: "Simplex4D") -> complex:
        """⟨ψ_i|ψ_j⟩ — full complex inner product."""
        return complex(np.vdot(self.psi, other.psi))

    # ── Derived geometric quantities (Derivation 4) ──────────────

    def ds_squared(self, other: "Simplex4D") -> float:
        """
        ds² = 1 - (d+1)·W_ij

        Emergent metric distance. (Derivation 4.2)
        Positive for distinct cells, zero for identical.
        """
        return 1.0 - self.N_VERTICES * self.W(other)

    def dihedral_angle(self, other: "Simplex4D") -> float:
        """
        θ_ij = arccos|⟨ψ_i|ψ_j⟩| = arccos√((d+1)·W_ij)

        Fubini-Study angle → dihedral angle. (Derivation 4.1)
        """
        w = self.W(other)
        cos_theta = np.sqrt(self.N_VERTICES * w)
        return float(np.arccos(np.clip(cos_theta, 0.0, 1.0)))

    def holonomy_phase(self, b: "Simplex4D", c: "Simplex4D") -> float:
        """
        Φ = arg(⟨a|b⟩⟨b|c⟩⟨c|a⟩)

        Gauge-invariant holonomy around triangle a→b→c. (Derivation 4.4)
        This is the discrete Wilson loop — seed of gauge theory.
        """
        ab = self.overlap(b)
        bc = b.overlap(c)
        ca = c.overlap(self)
        return float(np.angle(ab * bc * ca))

    # ── Gram matrix and hinge area (Derivation 4.4) ──────────────

    @staticmethod
    def gram_matrix(cells: list["Simplex4D"]) -> np.ndarray:
        """
        G_ij = ⟨ψ_i|ψ_j⟩

        Gram matrix of a set of cells. det(G) gives hinge area².
        """
        n = len(cells)
        G = np.zeros((n, n), dtype=np.complex128)
        for i in range(n):
            for j in range(n):
                G[i, j] = cells[i].overlap(cells[j])
        return G

    @staticmethod
    def hinge_area(cells: list["Simplex4D"]) -> float:
        """
        A_h = √det(G_h)

        Area of the hinge (triangle) formed by the given cells. (Derivation 4.4)
        """
        G = Simplex4D.gram_matrix(cells)
        det = np.linalg.det(G)
        return float(np.sqrt(max(0.0, det.real)))

    # ── Regge action contributions (Derivation 6) ────────────────

    def deficit_angle(self, neighbors: list["Simplex4D"]) -> float:
        """
        δ = 2π - Σ_k θ_k

        Deficit angle at this cell given its neighbors. (Derivation 4.3)
        Positive = positive curvature, negative = negative curvature.
        """
        theta_sum = sum(self.dihedral_angle(n) for n in neighbors)
        return 2.0 * np.pi - theta_sum

    def discrete_action_contribution(self, neighbors: list["Simplex4D"]) -> float:
        """
        S/ℏ per hinge = 4·δ  (area cancels! Derivation 6.2)

        The dimensionless action contribution. Scale-free, UV-finite.
        """
        return 4.0 * self.deficit_angle(neighbors)

    # ── ℏ_eff computation (Derivation 12) ────────────────────────

    def h_eff(self, boundary_neighbors: list["Simplex4D"],
              G_newton: float = 1.0, c_light: float = 1.0) -> float:
        """
        ℏ_eff = A·c³ / (4G·S_info)

        Computable effective Planck constant. (Derivation 12)
        """
        # Area: average hinge area with neighbors
        areas = [self.hinge_area([self, n]) for n in boundary_neighbors]
        A = sum(areas) if areas else 0.0

        # Information entropy: binary entropy of each link
        S_info = 0.0
        for n in boundary_neighbors:
            p = self.N_VERTICES * self.W(n)
            p = np.clip(p, 1e-15, 1.0 - 1e-15)
            S_info += -p * np.log(p) - (1 - p) * np.log(1 - p)

        if S_info < 1e-15:
            return float('inf')  # pure quantum limit

        return A * c_light**3 / (4.0 * G_newton * S_info)

    # ── 10-bit data bus (Derivation 11) ──────────────────────────

    @property
    def vertex_states(self) -> list[complex]:
        """The 5 complex registers (vertex data)."""
        return list(self.psi)

    def edge_weights(self) -> dict[tuple[int, int], float]:
        """
        All 10 pairwise |⟨e_i|e_j⟩|² within the simplex.

        NOT inter-cell W (which compares different simplices),
        but intra-vertex data: the 10 "metric components".
        For a single-cell state |ψ⟩ = Σ c_k|e_k⟩, the
        pairwise vertex correlations are c_i* c_j.
        """
        weights = {}
        for i, j in self.EDGES:
            # Correlation between vertex i and vertex j
            weights[(i, j)] = float(np.abs(self.psi[i] * np.conj(self.psi[j])) ** 2)
        return weights

    # ── Causal structure (Derivation 9, 10) ──────────────────────

    @property
    def temporal_state(self) -> np.ndarray:
        """SU(2) sector: the 2 temporal vertex components."""
        return self.psi[self.TEMPORAL_VERTICES]

    @property
    def spatial_state(self) -> np.ndarray:
        """SU(3) sector: the 3 spatial vertex components."""
        return self.psi[self.SPATIAL_VERTICES]

    @property
    def temporal_weight(self) -> float:
        """Σ|c_k|² for temporal vertices — energy-like. (Derivation 10)"""
        return float(np.sum(np.abs(self.temporal_state) ** 2))

    @property
    def spatial_weight(self) -> float:
        """Σ|c_k|² for spatial vertices — momentum-like. (Derivation 10)"""
        return float(np.sum(np.abs(self.spatial_state) ** 2))

    # ── Path integral weight (Derivation 6.5) ────────────────────

    def edge_boltzmann_weight(self, other: "Simplex4D") -> complex:
        """
        w(i,j) = exp(-4i·arccos|⟨ψ_i|ψ_j⟩|)

        The edge weight in the path integral. (Derivation 6.5)
        """
        theta = self.dihedral_angle(other)
        return np.exp(-4j * theta)

    # ── Display ───────────────────────────────────────────────────

    def __repr__(self) -> str:
        p = self.probabilities
        s = self.shannon_entropy
        tw = self.temporal_weight
        sw = self.spatial_weight
        return (
            f"Simplex4D(\n"
            f"  probabilities = [{', '.join(f'{x:.4f}' for x in p)}]\n"
            f"  shannon_entropy = {s:.4f} bits (max={np.log2(self.N_VERTICES):.4f})\n"
            f"  temporal_weight = {tw:.4f} (SU(2) sector)\n"
            f"  spatial_weight  = {sw:.4f} (SU(3) sector)\n"
            f")"
        )


# ── Quick verification ────────────────────────────────────────────

if __name__ == "__main__":
    print("=" * 60)
    print("DRLT Simplex4D — Axiom Verification")
    print("=" * 60)

    # Create two random simplices
    a = Simplex4D()
    b = Simplex4D()

    print(f"\nSimplex A:\n{a}")
    print(f"\nSimplex B:\n{b}")

    # Core axiom: W_ij
    w_ab = a.W(b)
    w_aa = a.W(a)
    print(f"\n── Axiom Verification ──")
    print(f"W(A,A) = {w_aa:.6f}  (should be 1/{a.N_VERTICES} = {1/a.N_VERTICES:.6f})")
    print(f"W(A,B) = {w_ab:.6f}  (range: [0, {1/a.N_VERTICES:.4f}])")
    print(f"W(B,A) = {b.W(a):.6f}  (should equal W(A,B): symmetric)")

    # Derivation 1: normalization
    print(f"\n── Derivation 1: Normalization ──")
    print(f"⟨A|A⟩ = {np.vdot(a.psi, a.psi):.6f}  (forced to 1)")

    # Derivation 4: metric
    ds2 = a.ds_squared(b)
    theta = a.dihedral_angle(b)
    print(f"\n── Derivation 4: Geometry ──")
    print(f"ds²(A,B) = {ds2:.6f}  (> 0 for distinct cells)")
    print(f"θ(A,B)   = {theta:.6f} rad = {np.degrees(theta):.2f}°")

    # Derivation 4.4: hinge area and holonomy
    c = Simplex4D()
    area = Simplex4D.hinge_area([a, b, c])
    phase = a.holonomy_phase(b, c)
    print(f"\n── Derivation 4.4: Hinge ──")
    print(f"A_h(A,B,C) = {area:.6f}  (hinge area)")
    print(f"Φ(A→B→C)  = {phase:.6f} rad  (holonomy = Wilson loop)")

    # Derivation 6: discrete action (area cancels!)
    delta = a.deficit_angle([b, c])
    action = a.discrete_action_contribution([b, c])
    print(f"\n── Derivation 6: Discrete Action ──")
    print(f"δ(A)   = {delta:.6f} rad  (deficit angle)")
    print(f"S/ℏ    = {action:.6f}  (purely angular, no lengths!)")

    # Derivation 10: SU(5) → SU(3) × SU(2) × U(1)
    print(f"\n── Derivation 10: Causal (2,3) Split ──")
    print(f"Temporal weight (SU(2)): {a.temporal_weight:.4f}")
    print(f"Spatial weight  (SU(3)): {a.spatial_weight:.4f}")
    print(f"Sum = {a.temporal_weight + a.spatial_weight:.4f}  (= 1 by normalization)")

    # Derivation 11: 10-bit data bus
    print(f"\n── Derivation 11: 10-Bit Data Bus ──")
    ew = a.edge_weights()
    for (i, j), w in ew.items():
        label = "T-T" if i < 2 and j < 2 else "S-S" if i >= 2 and j >= 2 else "T-S"
        print(f"  edge ({i},{j}) [{label}]: {w:.6f}")

    # Derivation 12: ℏ_eff
    h = a.h_eff([b, c])
    print(f"\n── Derivation 12: ℏ_eff ──")
    print(f"ℏ_eff = {h:.6f}  (in natural units G=c=1)")

    # Derivation 13: uncertainty bound
    print(f"\n── Derivation 13: Uncertainty ──")
    print(f"ℏ_eff/2 = {h/2:.6f}  (minimum ΔxΔp)")
    print(f"ℏ_eff > 0: {h > 0}  (quantum repulsion guaranteed)")

    # Verify orthogonal states → W = 0, ds² = 1
    print(f"\n── Edge Cases ──")
    e0 = Simplex4D(np.array([1, 0, 0, 0, 0], dtype=complex))
    e1 = Simplex4D(np.array([0, 1, 0, 0, 0], dtype=complex))
    print(f"Orthogonal: W = {e0.W(e1):.6f} (= 0), ds² = {e0.ds_squared(e1):.6f} (= 1)")

    same = Simplex4D(np.array([1, 0, 0, 0, 0], dtype=complex))
    print(f"Identical:  W = {e0.W(same):.6f} (= 1/5), ds² = {e0.ds_squared(same):.6f} (= 0)")

    print(f"\n{'=' * 60}")
    print(f"All quantities derived from one axiom: W_ij = |⟨ψ_i|ψ_j⟩|²/(d+1)")
    print(f"{'=' * 60}")
