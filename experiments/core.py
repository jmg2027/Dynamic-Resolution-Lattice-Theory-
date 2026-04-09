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

    # ── (2,3) causal split ─────────────────────────────────

    T_IDX = [0, 1]       # temporal vertices → SU(2)
    S_IDX = [2, 3, 4]    # spatial vertices  → SU(3)

    def overlap_T(self, other: "Vertex") -> complex:
        """Temporal sector overlap: Σ_{k∈T} c_k^(i)* c_k^(j)"""
        return complex(np.vdot(self.psi[self.T_IDX], other.psi[self.T_IDX]))

    def overlap_S(self, other: "Vertex") -> complex:
        """Spatial sector overlap: Σ_{k∈S} c_k^(i)* c_k^(j)"""
        return complex(np.vdot(self.psi[self.S_IDX], other.psi[self.S_IDX]))

    def interaction_decomposition(self, other: "Vertex") -> dict:
        """
        Decompose ⟨ψ_i|ψ_j⟩ into the four fundamental interactions.

        All four forces come from the SAME inner product,
        split by the (2,3) causal structure.
        """
        oT = self.overlap_T(other)
        oS = self.overlap_S(other)
        o_full = oT + oS  # = self.overlap(other)

        # Gravity: full overlap magnitude (all 5 vertices)
        gravity = float(np.abs(o_full) ** 2) / 5

        # Weak force: temporal sector (SU(2), 2 vertices)
        weak = float(np.abs(oT) ** 2) / 2

        # Strong force: spatial sector (SU(3), 3 vertices)
        strong = float(np.abs(oS) ** 2) / 3

        # Electromagnetism: relative phase between T and S sectors (U(1))
        phase_T = np.angle(oT) if np.abs(oT) > 1e-15 else 0.0
        phase_S = np.angle(oS) if np.abs(oS) > 1e-15 else 0.0
        em_phase = float(phase_T - phase_S)

        return {
            "gravity": gravity,       # W_ij (full)
            "weak": weak,             # W_T (SU(2) sector)
            "strong": strong,         # W_S (SU(3) sector)
            "em_phase": em_phase,     # arg(T/S) (U(1))
            "em_strength": float(np.abs(np.sin(em_phase))),
        }

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

    # ── Interaction decomposition (all 4 forces) ────────────

    def interaction_map(self) -> dict:
        """
        Decompose ALL pairwise interactions into the four forces.

        Gravity, weak, strong, EM all come from the SAME W_ij,
        split by the (2,3) causal structure of C⁵.
        """
        n = self.N
        grav, weak, strong, em = [], [], [], []

        for i in range(n):
            for j in range(i + 1, n):
                d = self.vertices[i].interaction_decomposition(self.vertices[j])
                grav.append(d["gravity"])
                weak.append(d["weak"])
                strong.append(d["strong"])
                em.append(d["em_strength"])

        return {
            "gravity":  {"mean": np.mean(grav),  "std": np.std(grav)},
            "weak":     {"mean": np.mean(weak),  "std": np.std(weak)},
            "strong":   {"mean": np.mean(strong), "std": np.std(strong)},
            "em":       {"mean": np.mean(em),    "std": np.std(em)},
        }

    @staticmethod
    def coupling_ratios() -> dict:
        """
        Coupling constant ratios from vertex counting.

        At the GUT scale (SU(5) unbroken), all vertices equivalent.
        Below GUT scale, (2,3) split gives:

          g_strong² ∝ 1/n_spatial  = 1/3
          g_weak²   ∝ 1/n_temporal = 1/2
          g_em²     ∝ 1/1          = 1

        With SU(5) normalization (U(1) factor √(3/5)):
          α₁ : α₂ : α₃ = (3/5) : 1 : 1  at GUT scale
        """
        return {
            "g_strong_sq": 1 / 3,
            "g_weak_sq": 1 / 2,
            "g_em_sq": 1.0,
            "ratio_strong_weak": (1/3) / (1/2),  # = 2/3
            "ratio_em_weak": 1.0 / (1/2),        # = 2
            "ratio_em_strong": 1.0 / (1/3),      # = 3
            "su5_normalized": {
                "alpha1": 3/5,  # with √(3/5) normalization
                "alpha2": 1.0,
                "alpha3": 1.0,
            },
        }

    # ── Pachner moves (topology change) ───────────────────────

    def pachner_1to5(self, vertex_ids: list[int]) -> int:
        """
        1→5 Pachner move: add a new vertex at the "center" of existing ones.

        ψ_new = normalized mean of neighbors → 0 new independent info.
        N increases by 1, but information is conserved.
        Resolution goes UP.
        """
        mean_psi = np.mean([self.vertices[i].psi for i in vertex_ids], axis=0)
        new_v = Vertex(mean_psi)  # normalized in __init__
        self.vertices.append(new_v)
        return len(self.vertices) - 1

    def pachner_5to1(self, vertex_ids: list[int],
                     w_threshold: float = 0.18) -> bool:
        """
        5→1 Pachner move: remove vertices that are nearly identical.

        Only allowed when the vertices' mutual W > threshold
        (i.e., ℏ_eff is small → states are indistinguishable).
        Returns True if merge happened.
        """
        # Check: are all pairs nearly identical?
        for i in range(len(vertex_ids)):
            for j in range(i + 1, len(vertex_ids)):
                w = self.vertices[vertex_ids[i]].W(self.vertices[vertex_ids[j]])
                if w < w_threshold:
                    return False  # not similar enough → move forbidden

        # Keep the first, remove the rest (sorted descending to avoid index shift)
        to_remove = sorted(vertex_ids[1:], reverse=True)
        for idx in to_remove:
            self.vertices.pop(idx)
        return True

    # ── The 10/8 ratio ────────────────────────────────────────

    @staticmethod
    def graviton_dof(d: int = 4) -> dict:
        """
        The 10/8 ratio and graviton polarizations.

        g_μν components:  d(d+1)/2
        CP^d dimension:   2d
        Difference:       d(d-3)/2 = graviton polarizations
        """
        g_components = d * (d + 1) // 2
        cp_dim = 2 * d
        graviton = d * (d - 3) // 2
        return {
            "d": d,
            "g_components": g_components,
            "cp_dim": cp_dim,
            "graviton_polarizations": graviton,
            "ratio": g_components / cp_dim,
        }

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

    # ── 7. Four forces from geometry ──────────────────────────
    print(f"\n[7] Four forces from W_ij decomposition")
    forces = net.interaction_map()
    print(f"    Gravity (full W):       mean = {forces['gravity']['mean']:.5f}")
    print(f"    Weak (SU(2) temporal):  mean = {forces['weak']['mean']:.5f}")
    print(f"    Strong (SU(3) spatial): mean = {forces['strong']['mean']:.5f}")
    print(f"    EM (U(1) phase):        mean = {forces['em']['mean']:.5f}")

    # Show one pair in detail
    print(f"\n    Example: vertices 0 and 1 (same cluster)")
    d = net.vertices[0].interaction_decomposition(net.vertices[1])
    for k, v in d.items():
        print(f"      {k:15s} = {v:.5f}")

    print(f"\n    Example: vertices 0 and 8 (different clusters)")
    d2 = net.vertices[0].interaction_decomposition(net.vertices[8])
    for k, v in d2.items():
        print(f"      {k:15s} = {v:.5f}")

    # ── 8. Coupling constant ratios ──────────────────────────
    print(f"\n[8] Coupling constants from vertex counting")
    cr = Network.coupling_ratios()
    print(f"    g_strong² ∝ 1/3 = {cr['g_strong_sq']:.4f}")
    print(f"    g_weak²   ∝ 1/2 = {cr['g_weak_sq']:.4f}")
    print(f"    g_em²     ∝ 1/1 = {cr['g_em_sq']:.4f}")
    print(f"    Ratio strong/weak = {cr['ratio_strong_weak']:.4f} (= 2/3)")
    print(f"    Ratio em/strong   = {cr['ratio_em_strong']:.4f} (= 3)")

    # ── 9. Graviton polarizations ─────────────────────────────
    print(f"\n[9] Graviton polarizations (the 10/8 ratio)")
    for d_dim in [3, 4, 5, 6]:
        g = Network.graviton_dof(d_dim)
        print(f"    d={d_dim}: g_μν={g['g_components']:2d}, "
              f"CP^d={g['cp_dim']:2d}, "
              f"graviton={g['graviton_polarizations']} polarizations")
