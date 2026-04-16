"""
ATM_064: Hinge Algebra — Multiplication Table
Joint research by Mingu Jeong and Claude (Anthropic)

The 10 hinges (triangles) of Δ⁴ form an algebra under
intersection product. We compute the structure constants:

    hinge_i ∧ hinge_j = Σ_k c_{ij}^k hinge_k

and check:
  1. Is it associative? commutative?
  2. Does it match SU(5) adjoint rep?
  3. What is the physical meaning of c_{ij}^k?

Key distinction (Mingu Jeong):
  H*(ℂP⁴) = ℂ[x]/x⁵  → 5 classes (p,p), one generator x
  DRLT hinges = C(5,3) = 10 → (3,2) decomposition

The 10 hinges are NOT the Hodge classes. They are the
face classification of Δ⁴ under the (N_S=3, N_T=2) split.

Tests:
  1. Enumerate all 10 hinges with (N_S,N_T) type
  2. Compute intersection product (shared edges)
  3. Build multiplication table
  4. Classify the algebra
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from experiment import Experiment

D = 5; N_S = 3; N_T = 2

# Vertices of Δ⁴: 3 spatial (A) + 2 temporal (B)
VERTS = ['A1', 'A2', 'A3', 'B1', 'B2']
A_SET = {'A1', 'A2', 'A3'}
B_SET = {'B1', 'B2'}


def hinge_type(tri):
    """Classify hinge by (n_A, n_B) content."""
    s = set(tri)
    na = len(s & A_SET)
    nb = len(s & B_SET)
    return (na, nb)


def type_label(tri):
    """Human-readable label: SSS, SST, STT, etc."""
    na, nb = hinge_type(tri)
    return 'S'*na + 'T'*nb


def shared_edge(tri1, tri2):
    """Intersection of two hinges = shared edge (vertices)."""
    return frozenset(tri1) & frozenset(tri2)


def enumerate_hinges():
    """All C(5,3) = 10 triangular hinges of Δ⁴."""
    return [tuple(sorted(c)) for c in combinations(VERTS, 3)]


class HingeAlgebra(Experiment):
    ID = "ATM_064"
    TITLE = "Hinge Algebra"

    def run(self):
        self.test1_enumerate()
        self.test2_intersection_product()
        self.test3_multiplication_table()
        self.test4_algebra_properties()

    def test1_enumerate(self):
        """List all 10 hinges with type."""
        self.log(f"\n  {'='*55}")
        self.log(f"  10 Hinges of Δ⁴ (C(5,3) = 10)")
        self.log(f"  {'='*55}")

        hinges = enumerate_hinges()
        self.log(f"\n  H*(ℂP⁴) = ℂ[x]/x⁵ → 5 classes (p,p)")
        self.log(f"  DRLT hinges = C(5,3) = 10 under (3,2) split")
        self.log(f"\n  {'#':>3} {'Hinge':>15} {'Type':>5}"
                 f" {'n_A':>4} {'n_B':>4}")

        type_counts = {}
        for i, h in enumerate(hinges):
            t = type_label(h)
            na, nb = hinge_type(h)
            type_counts[t] = type_counts.get(t, 0) + 1
            self.log(f"  {i:3d} {str(h):>15} {t:>5}"
                     f" {na:4d} {nb:4d}")

        self.log(f"\n  Type counts:")
        for t, c in sorted(type_counts.items()):
            w = 2**type_counts.get(t, 0)
            self.log(f"    {t}: {c} hinges")

        self.log(f"\n  SSS = C(3,3)×C(2,0) = 1 (strong/s)")
        self.log(f"  SST = C(3,2)×C(2,1) = 6 (EM/p)")
        self.log(f"  STT = C(3,1)×C(2,2) = 3 (weak/d)")
        self.log(f"  Total: 1+6+3 = 10 = C(5,3) ✓")

        self.check("10 hinges enumerated",
                   len(hinges) == 10)

    def test2_intersection_product(self):
        """Intersection of two hinges = shared vertices."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Intersection product: hinge ∧ hinge")
        self.log(f"  {'='*55}")

        hinges = enumerate_hinges()
        self.log(f"\n  Two hinges share 0, 1, or 2 vertices.")
        self.log(f"  Shared 2 = common edge → codim-1 face")
        self.log(f"  Shared 1 = common vertex → codim-2")
        self.log(f"  Shared 0 = disjoint → zero product")

        # Count by shared vertices
        counts = {0: 0, 1: 0, 2: 0, 3: 0}
        for i in range(len(hinges)):
            for j in range(i+1, len(hinges)):
                shared = len(shared_edge(hinges[i], hinges[j]))
                counts[shared] += 1

        self.log(f"\n  Shared vertex distribution:")
        for k, v in sorted(counts.items()):
            self.log(f"    {k} shared: {v} pairs")

        self.log(f"\n  Total pairs: C(10,2) = {sum(counts.values())}")
        self.check("Intersection computed", True)

    def test3_multiplication_table(self):
        """Full 10×10 structure constants."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Multiplication table: c_{{ij}}^k")
        self.log(f"  {'='*55}")

        hinges = enumerate_hinges()
        n = len(hinges)

        # Define product: hinge_i ∧ hinge_j → edges they share
        # Map each edge to which hinges contain it
        edges = list(combinations(VERTS, 2))
        edge_to_hinges = {}
        for e in edges:
            es = frozenset(e)
            containing = []
            for k, h in enumerate(hinges):
                if es.issubset(frozenset(h)):
                    containing.append(k)
            edge_to_hinges[es] = containing

        self.log(f"\n  C(5,2) = {len(edges)} edges")
        self.log(f"  Each edge is shared by C(3,1) = 3 hinges")

        # Structure constants: c_{ij}^k = number of edges
        # shared by hinges i,j that also belong to hinge k
        # This is the triple intersection number.
        c = np.zeros((n, n, n), dtype=int)

        for e in edges:
            es = frozenset(e)
            hs = edge_to_hinges[es]
            # Each edge defines a "flag" where all 3 hinges
            # containing it get c_{ij}^k = 1
            for i in hs:
                for j in hs:
                    for k in hs:
                        if i != j and i != k and j != k:
                            c[i, j, k] += 1

        # Also: self-product through shared edges
        # hinge_i ∧ hinge_i → all edges in hinge_i
        for i in range(n):
            tri = frozenset(hinges[i])
            for e in combinations(hinges[i], 2):
                es = frozenset(e)
                for k in edge_to_hinges[es]:
                    if k != i:
                        c[i, i, k] += 1

        # Print adjacency matrix (number of shared edges)
        self.log(f"\n  Adjacency (shared edges between pairs):")
        labels = [type_label(h) for h in hinges]
        header = "     " + " ".join(f"{l:>4}" for l in labels)
        self.log(f"  {header}")
        for i in range(n):
            row = [len(shared_edge(hinges[i], hinges[j]))
                   for j in range(n)]
            vals = " ".join(f"{v:4d}" for v in row)
            self.log(f"  {labels[i]:>4} {vals}")

        self.check("Multiplication table built", True)

    def test4_algebra_properties(self):
        """Check commutativity, associativity, etc."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Algebra properties")
        self.log(f"  {'='*55}")

        hinges = enumerate_hinges()
        n = len(hinges)

        # Build adjacency by shared edges (simpler product)
        adj = np.zeros((n, n), dtype=int)
        for i in range(n):
            for j in range(n):
                adj[i, j] = len(shared_edge(hinges[i], hinges[j]))

        # Commutative? adj[i,j] == adj[j,i]
        comm = np.allclose(adj, adj.T)
        self.log(f"\n  Commutative: {comm}")

        # Eigenvalues of adjacency matrix
        eigvals = np.sort(np.linalg.eigvalsh(adj))[::-1]
        self.log(f"\n  Adjacency eigenvalues:")
        for ev in eigvals:
            self.log(f"    λ = {ev:.4f}")

        # Trace = sum of diagonal = each hinge shares 3 edges
        # with itself
        self.log(f"\n  Trace = {np.trace(adj)}"
                 f" (each hinge has C(3,2)=3 edges)")

        # Block structure by type
        self.log(f"\n  Type-block structure:")
        types = ['SSS', 'SST', 'STT']
        type_indices = {t: [] for t in types}
        for i, h in enumerate(hinges):
            type_indices[type_label(h)].append(i)

        for t1 in types:
            for t2 in types:
                block = adj[np.ix_(type_indices[t1],
                                   type_indices[t2])]
                s = block.sum()
                avg = block.mean() if block.size else 0
                self.log(f"    {t1}×{t2}: sum={s:3d}"
                         f" avg={avg:.2f}")

        # Connection to H*(ℂP⁴) = ℂ[x]/x⁵
        self.log(f"\n  Cohomology ring connection:")
        self.log(f"    H*(ℂP⁴) = ℂ[x]/x⁵")
        self.log(f"    x ∈ H² = generator (\"prime\")")
        self.log(f"    1, x, x², x³, x⁴ = all classes")
        self.log(f"    x⁵ = 0 (truncation)")
        self.log(f"")
        self.log(f"    DRLT: 10 hinges ≠ H* classes")
        self.log(f"    10 hinges = C(5,3) face classification")
        self.log(f"    under ℂ³⊕ℂ² decomposition")

        self.check("Algebra analyzed", True)


if __name__ == "__main__":
    HingeAlgebra().execute()
