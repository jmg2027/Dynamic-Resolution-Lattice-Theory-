"""
DRLT Core — The True Foundation
================================

Refined Axiom:
  N vertices exist. Each carries |ψ⟩ ∈ C⁵.
  W_ij = |⟨ψ_i|ψ_j⟩|² / d   for all pairs.
  That's it.

Simplices are NOT input. They are patterns discovered
in the W_ij weighted complete graph (high-W 5-cliques).
Spacetime is output, not input.
"""

import numpy as np
from itertools import combinations


# ═══════════════════════════════════════════════════════════════
#  VERTEX: The only fundamental object
# ═══════════════════════════════════════════════════════════════

class Vertex:
    """
    A single vertex carrying |ψ⟩ ∈ C⁵.

    This is the ONLY fundamental entity in DRLT.
    Everything else — W, metric, simplices, curvature,
    spacetime — emerges from collections of vertices.
    """

    DIM = 5  # C⁵ (= d+1, where d=4 spacetime dimensions)

    def __init__(self, psi: np.ndarray | None = None):
        if psi is None:
            psi = self._random_state()
        self.psi = self._normalize(psi.astype(np.complex128))

    @staticmethod
    def _normalize(psi: np.ndarray) -> np.ndarray:
        norm = np.linalg.norm(psi)
        if norm < 1e-15:
            raise ValueError("Zero vector")
        return psi / norm

    @staticmethod
    def _random_state() -> np.ndarray:
        return np.random.randn(5) + 1j * np.random.randn(5)

    def overlap(self, other: "Vertex") -> complex:
        """⟨ψ_i|ψ_j⟩"""
        return complex(np.vdot(self.psi, other.psi))

    def W(self, other: "Vertex") -> float:
        """W_ij = |⟨ψ_i|ψ_j⟩|² / d  — THE AXIOM."""
        return float(np.abs(self.overlap(other)) ** 2) / self.DIM

    def ds2(self, other: "Vertex") -> float:
        """ds² = 1 - d·W_ij  — emergent metric."""
        return 1.0 - self.DIM * self.W(other)

    def angle(self, other: "Vertex") -> float:
        """θ = arccos|⟨ψ_i|ψ_j⟩| — Fubini-Study angle."""
        cos_t = min(1.0, np.sqrt(self.DIM * self.W(other)))
        return float(np.arccos(cos_t))

    def phase(self, other: "Vertex") -> float:
        """arg⟨ψ_i|ψ_j⟩ — gauge connection."""
        return float(np.angle(self.overlap(other)))

    @property
    def shannon_entropy(self) -> float:
        p = np.abs(self.psi) ** 2
        p = p[p > 1e-15]
        return float(-np.sum(p * np.log2(p)))

    def __repr__(self):
        return f"Vertex(S={self.shannon_entropy:.2f}bits)"


# ═══════════════════════════════════════════════════════════════
#  NETWORK: Weighted complete graph of vertices
# ═══════════════════════════════════════════════════════════════

class Network:
    """
    N vertices, all pairwise connected by W_ij.
    This IS the universe. Simplices are found, not placed.
    """

    def __init__(self, n: int = 0, vertices: list[Vertex] | None = None):
        if vertices is not None:
            self.vertices = list(vertices)
        else:
            self.vertices = [Vertex() for _ in range(n)]

    @property
    def N(self) -> int:
        return len(self.vertices)

    # ── The W matrix (the universe itself) ────────────────────

    def W_matrix(self) -> np.ndarray:
        """Full W_ij for all pairs. This encodes everything."""
        n = self.N
        W = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                W[i, j] = self.vertices[i].W(self.vertices[j])
        return W

    def ds2_matrix(self) -> np.ndarray:
        """Emergent metric between all pairs."""
        return 1.0 - Vertex.DIM * self.W_matrix()

    # ── Simplex discovery ─────────────────────────────────────

    def find_simplices(self, w_threshold: float = 0.04) -> list[tuple[int, ...]]:
        """
        Discover 4-simplices as high-W 5-cliques.

        A 5-clique {i,j,k,l,m} is a simplex if ALL 10
        pairwise W values exceed w_threshold.

        Simplices are NOT input — they emerge from the W pattern.
        """
        n = self.N
        W = self.W_matrix()
        simplices = []

        for combo in combinations(range(n), 5):
            # Check all 10 pairs
            is_simplex = True
            for a, b in combinations(combo, 2):
                if W[a, b] < w_threshold:
                    is_simplex = False
                    break
            if is_simplex:
                simplices.append(combo)

        return simplices

    def find_shared_faces(self, simplices: list[tuple[int, ...]]
                          ) -> list[tuple[int, int, tuple[int, ...]]]:
        """
        Find pairs of simplices sharing a tetrahedron (4 common vertices).
        This is the adjacency structure of the simplicial complex.
        """
        faces = []
        for a in range(len(simplices)):
            sa = set(simplices[a])
            for b in range(a + 1, len(simplices)):
                sb = set(simplices[b])
                shared = sa & sb
                if len(shared) >= 4:
                    faces.append((a, b, tuple(sorted(shared))))
        return faces

    # ── Curvature from discovered simplices ───────────────────

    def find_hinges(self, simplices: list[tuple[int, ...]]
                    ) -> dict[tuple[int, ...], list[int]]:
        """
        Find hinges (triangles) and which simplices share each.

        A hinge is a triangle (3 vertices) shared by multiple simplices.
        The number of simplices around a hinge → curvature.
        """
        hinge_map: dict[tuple[int, ...], list[int]] = {}

        for idx, simplex in enumerate(simplices):
            # Each 4-simplex has C(5,3)=10 triangles
            for tri in combinations(simplex, 3):
                key = tuple(sorted(tri))
                if key not in hinge_map:
                    hinge_map[key] = []
                hinge_map[key].append(idx)

        # Only keep hinges shared by 2+ simplices (interior hinges)
        return {k: v for k, v in hinge_map.items() if len(v) >= 2}

    def deficit_angle(self, hinge_simplices: list[int],
                      simplices: list[tuple[int, ...]]) -> float:
        """
        δ = 2π - Σ θ_k for simplices around a hinge.

        The dihedral angle between two simplices sharing a face
        is computed from their "unique" vertices (the ones not shared).
        """
        n = len(hinge_simplices)
        if n < 2:
            return 2 * np.pi

        theta_sum = 0.0
        for k in range(n):
            for l in range(k + 1, n):
                sa = set(simplices[hinge_simplices[k]])
                sb = set(simplices[hinge_simplices[l]])
                # Unique vertices of each simplex (not shared)
                ua = sa - sb
                ub = sb - sa
                if ua and ub:
                    # Dihedral angle from the unique vertices' states
                    vi = list(ua)[0]
                    vj = list(ub)[0]
                    theta_sum += self.vertices[vi].angle(self.vertices[vj])

        return 2 * np.pi - theta_sum

    def curvature_map(self, simplices: list[tuple[int, ...]]
                      ) -> list[tuple[tuple[int, ...], float, int]]:
        """
        Compute deficit angle at every interior hinge.
        Returns: [(triangle_vertices, deficit_angle, n_simplices_around), ...]
        """
        hinges = self.find_hinges(simplices)
        result = []
        for tri, simplex_ids in hinges.items():
            delta = self.deficit_angle(simplex_ids, simplices)
            result.append((tri, delta, len(simplex_ids)))
        return result

    # ── Global observables ────────────────────────────────────

    def total_info(self) -> float:
        """Total Shannon entropy across all vertices."""
        return sum(v.shannon_entropy for v in self.vertices)

    def mean_W(self) -> float:
        """Mean off-diagonal W."""
        W = self.W_matrix()
        n = self.N
        if n < 2:
            return 0.0
        mask = ~np.eye(n, dtype=bool)
        return float(np.mean(W[mask]))

    def min_ds2(self) -> float:
        """Minimum ds² (closest pair)."""
        ds2 = self.ds2_matrix()
        np.fill_diagonal(ds2, 999)
        return float(np.min(ds2)) if self.N > 1 else 1.0


# ═══════════════════════════════════════════════════════════════
#  DEMO
# ═══════════════════════════════════════════════════════════════

def make_clustered_network(n_clusters: int = 3, per_cluster: int = 6,
                           spread: float = 0.3) -> Network:
    """
    Create a network with clusters of nearby vertices.
    Within each cluster, ψ values are similar (high W → simplices form).
    Between clusters, ψ values differ (low W → separated regions).
    """
    verts = []
    for c in range(n_clusters):
        # Cluster center: a random state
        center = Vertex._random_state()
        center = center / np.linalg.norm(center)
        for _ in range(per_cluster):
            noise = (np.random.randn(5) + 1j * np.random.randn(5)) * spread
            verts.append(Vertex(center + noise))
    return Network(vertices=verts)


if __name__ == "__main__":
    np.random.seed(42)

    print("=" * 60)
    print("  DRLT Core: Vertices → W → Simplices (Emergent)")
    print("=" * 60)

    # ── 1. Create vertices with cluster structure ─────────────
    print("\n[1] Create 3 clusters × 6 vertices = 18 vertices")
    net = make_clustered_network(n_clusters=3, per_cluster=6, spread=0.3)
    n = net.N
    for i, v in enumerate(net.vertices):
        cluster = i // 6
        print(f"    v{i:2d} [cluster {cluster}]: {v}")

    # ── 2. W matrix (this IS the universe) ────────────────────
    pairs = n * (n - 1) // 2
    print(f"\n[2] W matrix ({n}×{n} = {pairs} unique pairs)")
    W = net.W_matrix()
    offdiag = W[~np.eye(n, dtype=bool)]
    print(f"    W diagonal:    {W[0,0]:.5f} (= 1/d = 1/5)")
    print(f"    W off-diag:    mean={net.mean_W():.5f}, "
          f"range=[{offdiag.min():.5f}, {offdiag.max():.5f}]")

    # Show cluster structure in W
    print(f"\n    Intra-cluster W (same cluster, should be HIGH):")
    for c in range(3):
        intra = [W[i, j] for i in range(c*6, (c+1)*6)
                 for j in range(i+1, (c+1)*6)]
        print(f"      cluster {c}: mean W = {np.mean(intra):.5f}")
    inter = [W[i, j] for i in range(6) for j in range(6, n)]
    print(f"    Inter-cluster W (different clusters, should be LOW):")
    print(f"      mean W = {np.mean(inter):.5f}")

    # ── 3. Discover simplices from W pattern ──────────────────
    print(f"\n[3] Simplex discovery (find high-W 5-cliques)")
    for thresh in [0.01, 0.02, 0.03, 0.04, 0.05]:
        simplices = net.find_simplices(w_threshold=thresh)
        print(f"    threshold W > {thresh:.2f}: "
              f"{len(simplices)} simplices found")

    # Use a reasonable threshold
    thresh = 0.03
    simplices = net.find_simplices(w_threshold=thresh)
    print(f"\n    Using threshold={thresh}:")
    for idx, s in enumerate(simplices[:10]):
        print(f"      simplex {idx}: vertices {s}")
    if len(simplices) > 10:
        print(f"      ... and {len(simplices)-10} more")

    # ── 4. Shared faces → adjacency ──────────────────────────
    print(f"\n[4] Shared faces (simplices sharing a tetrahedron)")
    faces = net.find_shared_faces(simplices)
    print(f"    {len(faces)} shared faces found")
    for a, b, shared in faces[:5]:
        print(f"      simplex {a} ↔ {b}: share vertices {shared}")

    # ── 5. Hinges and curvature ──────────────────────────────
    print(f"\n[5] Curvature at hinges (triangles shared by 2+ simplices)")
    curv = net.curvature_map(simplices)
    if curv:
        deficits = [d for _, d, _ in curv]
        print(f"    {len(curv)} interior hinges")
        print(f"    deficit angle: mean={np.degrees(np.mean(deficits)):+.1f}°, "
              f"range=[{np.degrees(min(deficits)):+.1f}°, "
              f"{np.degrees(max(deficits)):+.1f}°]")
        for tri, delta, n_simp in curv[:5]:
            print(f"      hinge {tri}: δ={np.degrees(delta):+.1f}°, "
                  f"{n_simp} simplices around")
    else:
        print("    No interior hinges (simplices don't share enough faces)")

    # ── 6. The key point ─────────────────────────────────────
    print(f"\n[6] Summary")
    print(f"    Input:  {net.N} vertices with ψ ∈ C⁵")
    print(f"    Found:  {len(simplices)} simplices (W > {thresh})")
    print(f"    Found:  {len(faces)} shared faces")
    print(f"    Found:  {len(curv)} hinges with curvature")
    print(f"    Total info: {net.total_info():.2f} bits")
    print(f"    min ds²: {net.min_ds2():.5f} > 0 (no singularity)")
    print()
    print("    Simplices were DISCOVERED, not placed.")
    print("    Spacetime is OUTPUT, not INPUT.")
