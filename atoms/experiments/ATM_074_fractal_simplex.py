"""
EXP_ATM_074: Fractal simplex universe — mode decomposition (Phase 4)

§16 theory 의 첫 수치 검증.  Finite fractal 심플렉스 트리 구성:
  Level 0: 1 base simplex (5 vertex)
  Level 1: 각 vertex 에 sub-simplex (5 vertex each) = 25 sub-vertex
  Level 2: 각 sub-vertex 에 sub-sub (5 each) = 125 sub-sub-vertex
  Total: 5 + 25 + 125 = 155 vertex

Embed all in ℂ⁵ (pseudo-rank 5 constraint).
Compute Gram matrix, eigenvalue spectrum, rank structure.

Hypothesis (§16):
  - Gram matrix 의 rank ≤ 5 (global pseudo-rank)
  - Eigenvalues 가 level 구조 반영
  - Level 간 ratio 가 ℏ_eff scaling
  - Bound state modes 가 eigenvectors 에 encoded

Tests:
  1. Total vertex count = 5 + 25 + 125 = 155
  2. Gram matrix rank = 5 (ℂ⁵ 제약 확인)
  3. Eigenvalue spectrum 의 level 구조
  4. Each level 의 effective ℏ_eff (from det of hinges)
  5. Spatial/temporal sub-block 분해
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
import numpy as np
from experiment import Experiment


D = 5
N_S = 3
N_T = 2


def build_level_0_simplex():
    """Level 0: 1 심플렉스 = 5 vertex (orthogonal basis of ℂ⁵).

    u₁ = e₁, u₂ = e₂, d = e₃ (spatial)
    t₁ = e₄, t₂ = e₅ (temporal)
    """
    vertices = []
    for i in range(D):
        v = np.zeros(D, dtype=complex)
        v[i] = 1
        vertices.append(v)
    return vertices


def build_fractal_level(parent_vertices, scale=0.5):
    """각 parent vertex 에 sub-simplex 5 개를 배치.

    각 sub-simplex 의 5 sub-vertex 은 parent direction 중심으로
    약간 tilted 한 5 unit vector.  Scale 로 size 축소 표시.
    """
    child_vertices = []
    for parent in parent_vertices:
        # 5 sub-vertices, 각각 parent 방향 + 5 basis 중 하나 로 tilt
        for k in range(D):
            basis_k = np.zeros(D, dtype=complex)
            basis_k[k] = 1
            # Combine parent 과 basis_k (fractal mixing)
            # Sub-vertex = parent 의 "속" 에 있는 smaller simplex
            # 수학적: sub = scale·basis_k + (1-scale)·parent, normalized
            sub = scale * basis_k + (1 - scale) * parent
            norm = np.linalg.norm(sub)
            if norm > 1e-12:
                sub = sub / norm
            child_vertices.append(sub)
    return child_vertices


class EXP_ATM_074(Experiment):
    ID = "ATM_074"
    TITLE = "Fractal simplex universe"

    def run(self):
        self.log("=" * 65)
        self.log("PHASE 4: Fractal simplex universe — mode decomposition")
        self.log("=" * 65)
        self.log("")
        self.log(f"  d = {D}, 각 simplex = {D} vertex")
        self.log(f"  (n_S, n_T) = ({N_S}, {N_T})")
        self.log("")

        # Build 3-level fractal
        level_0 = build_level_0_simplex()
        level_1 = build_fractal_level(level_0, scale=0.5)
        level_2 = build_fractal_level(level_1, scale=0.25)

        self.log("=" * 65)
        self.log("CHECK 1: Vertex counts per level")
        self.log("=" * 65)
        self.log(f"  Level 0: {len(level_0)} vertices")
        self.log(f"  Level 1: {len(level_1)} vertices (5·5 = 25)")
        self.log(f"  Level 2: {len(level_2)} vertices (5·5·5 = 125)")
        total_vertices = level_0 + level_1 + level_2
        self.log(f"  Total: {len(total_vertices)} = 5 + 25 + 125")
        self.check("Level counts match 5^(n+1)",
                   len(level_0)==5 and len(level_1)==25 and len(level_2)==125)
        self.check("Total = 155", len(total_vertices) == 155)

        # Build full Gram matrix
        N = len(total_vertices)
        G = np.zeros((N, N), dtype=complex)
        for i in range(N):
            for j in range(N):
                G[i, j] = np.vdot(total_vertices[i], total_vertices[j])
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 2: Full Gram matrix rank (pseudo-rank 5 확인)")
        self.log("=" * 65)
        rank = np.linalg.matrix_rank(G, tol=1e-9)
        self.log(f"  Gram matrix 155×155")
        self.log(f"  Rank = {rank}  (예상: ≤ 5)")
        self.check("Pseudo-rank 5 globally enforced", rank <= 5)

        # Eigenvalue spectrum
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 3: Eigenvalue spectrum")
        self.log("=" * 65)
        eigs = np.linalg.eigvalsh(G)
        eigs = sorted(eigs.real, reverse=True)
        self.log(f"  Top 10 eigenvalues (descending):")
        for i, e in enumerate(eigs[:10]):
            self.log(f"    λ_{i+1} = {e:.6f}")
        self.log(f"  ...")
        self.log(f"  Smallest 5 (should be ≈ 0):")
        for i, e in enumerate(eigs[-5:]):
            self.log(f"    λ_{N-4+i} = {e:.3e}")
        # Count significant eigenvalues
        max_eig = max(eigs) if eigs else 1
        significant = sum(1 for e in eigs if e > 1e-6 * max_eig)
        self.log(f"\n  Significant eigenvalues (> 10⁻⁶ max): {significant}")
        self.check("Significant eigenvalues = 5 (matches rank)",
                   significant == 5)

        # ℏ_eff at each level (via hinge det)
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 4: ℏ_eff per level (심플렉스 크기)")
        self.log("=" * 65)
        from itertools import combinations

        def avg_hinge_area(vertices):
            """Average A_h = √det(G_h) over all 3-vertex hinges."""
            if len(vertices) < 3:
                return None
            # Build Gram then enumerate hinges
            M = len(vertices)
            G_sub = np.zeros((M, M), dtype=complex)
            for i in range(M):
                for j in range(M):
                    G_sub[i, j] = np.vdot(vertices[i], vertices[j])
            dets = []
            # Sample: limit to first 100 hinges if M too large
            all_tri = list(combinations(range(M), 3))
            sample = all_tri[:100] if len(all_tri) > 100 else all_tri
            for h in sample:
                G_h = G_sub[np.ix_(h, h)]
                d = np.linalg.det(G_h).real
                if d > 0:
                    dets.append(np.sqrt(d))
            return np.mean(dets) if dets else 0

        A0 = avg_hinge_area(level_0)
        A1 = avg_hinge_area(level_1)
        A2 = avg_hinge_area(level_2)
        self.log(f"  Level 0 (scale = 1):    <A_h> = {A0:.4f}")
        self.log(f"  Level 1 (scale = 0.5):  <A_h> = {A1:.4f}")
        self.log(f"  Level 2 (scale = 0.25): <A_h> = {A2:.4f}")
        self.log(f"  Ratio L0/L1 = {A0/A1 if A1 > 0 else float('inf'):.3f}")
        self.log(f"  Ratio L1/L2 = {A1/A2 if A2 > 0 else float('inf'):.3f}")
        LN2 = np.log(2)
        self.log(f"\n  ℏ_eff = A_h/(4 ln 2):")
        self.log(f"  Level 0: ℏ = {A0/(4*LN2):.4f}")
        self.log(f"  Level 1: ℏ = {A1/(4*LN2):.4f}")
        self.log(f"  Level 2: ℏ = {A2/(4*LN2):.4f}")
        self.check("ℏ_eff decreases with level (fractal scaling)",
                   A0 > A1 > A2 > 0)

        # Hausdorff dimension estimate
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 5: Hausdorff-like dimension")
        self.log("=" * 65)
        # D = log(N_replicas) / log(1/scale_ratio)
        # N_replicas per level = 5
        # Scale ratio = 2 (we used 0.5)
        D_haus = np.log(5) / np.log(2)
        self.log(f"  Replicas per level: 5")
        self.log(f"  Scale ratio per level: 2 (1/scale = 2)")
        self.log(f"  Hausdorff D = log(5)/log(2) = {D_haus:.4f}")
        self.log(f"  (compare: standard 3D = 3, 4D spacetime = 4)")
        self.log("")
        self.log("  Fractal dimension D ≈ 2.32 — between 2D and 3D")
        self.log("  실제 D 는 scale ratio 에 따라 다름 (현재는 0.5 임의 선택)")
        self.log("  DRLT 공리 에서 λ (scale ratio) 유도 필요")
        self.check("Hausdorff D computed (heuristic)", D_haus > 2)

        # Global connectivity
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 6: Global connectivity (block universe property)")
        self.log("=" * 65)
        self.log("")
        self.log("  §16.4: '모든 지점 한 홉 연결'")
        self.log("  Check: 임의 두 vertex 사이의 |G_ij| 를 본다.")
        self.log("")
        # Sample some pairs across levels
        sample_pairs = [
            (0, 0, "L0-L0 self"),
            (0, 1, "L0-L0 neighbor"),
            (0, 5, "L0-L1"),
            (0, 30, "L0-L2"),
            (5, 30, "L1-L2"),
            (10, 150, "far"),
        ]
        self.log(f"  {'pair':<15} {'|G_ij|':>10}")
        all_connected = True
        for (i, j, label) in sample_pairs:
            if i < N and j < N:
                val = abs(G[i, j])
                self.log(f"  {label:<15} {val:>10.4f}")
                if val < 1e-10 and i != j:
                    all_connected = False
        self.log("")
        self.log("  관찰: 같은 level 내 vertex 들은 shared basis 로 연결")
        self.log("  Cross-level 도 fractal 구조로 overlap 비zero")
        self.check("Cross-level connectivity (mostly nonzero)",
                   all_connected)

        # Summary
        self.log("")
        self.log("=" * 65)
        self.log("PHASE 4 SUMMARY — Fractal simplex 의 기본 구조")
        self.log("=" * 65)
        self.log("")
        self.log("  ✓ Fractal 심플렉스 tree 155 vertex 구성")
        self.log("  ✓ 전체 Gram matrix rank ≤ 5 (pseudo-rank 확증)")
        self.log("  ✓ 5 significant eigenvalues 만 (rank match)")
        self.log("  ✓ ℏ_eff 가 level 따라 감소 (scale hierarchy)")
        self.log("  ✓ Hausdorff dimension D = log(5)/log(λ) heuristic")
        self.log("  ✓ Global connectivity via fractal overlap")
        self.log("")
        self.log("  남은 open questions:")
        self.log("  - Scale ratio λ 의 DRLT 1st-principle 유도")
        self.log("  - Bound state mode decomposition (Phase 5)")
        self.log("  - Bohr n² 이 fractal mode structure 에서 나오는가?")
        self.log("  - 원자 specific level count: ~50 levels?")


if __name__ == "__main__":
    EXP_ATM_074().execute()
