"""
NUC_001: 600-Cell Shell Analysis for Nuclear Magic Numbers
==========================================================
The 600-cell is a regular 4-polytope with 120 = d! = 5! vertices.
Binary icosahedral group 2I ≅ SL(2,5) acts on these vertices.

Key question: do the shell/sub-shell closing conditions of the
600-cell reproduce the nuclear magic numbers 2, 8, 20, 28, 50, 82, 126?

DRLT connections:
  - 120 = d! (d=5 is the DRLT dimension)
  - 600-cell lives in ℝ⁴ = ℝ^(d-1)
  - 2I is the double cover of A_d = Alt(5)
  - Each vertex ↔ one nucleon state (×2 for spin → 240 states)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np
from itertools import permutations

MAGIC_NUMBERS = [2, 8, 20, 28, 50, 82, 126]
PHI = (1 + np.sqrt(5)) / 2  # golden ratio


class NUC001(Experiment):
    ID = "NUC_001"
    TITLE = "600-Cell Shell Analysis"

    def run(self):
        self.log("\n=== Part 1: Construct 600-cell vertices ===")
        verts = self.build_600cell()
        self.check(f"120 vertices constructed", len(verts) == 120)

        self.log("\n=== Part 2: Distance shells from a vertex ===")
        self.analyze_vertex_shells(verts)

        self.log("\n=== Part 3: Adjacency spectrum ===")
        self.analyze_adjacency(verts)

        self.log("\n=== Part 4: Tetrahedral cell shells ===")
        self.analyze_cell_shells(verts)

        self.log("\n=== Part 5: Sub-shell decomposition (icosahedral irreps) ===")
        self.analyze_subshells(verts)

        self.log("\n=== Part 6: DRLT magic number candidates ===")
        self.magic_number_search(verts)

    # ── Part 1: Build 600-cell ──────────────────────────────────
    def build_600cell(self):
        """Construct 120 vertices of the 600-cell as unit quaternions in ℝ⁴.

        The vertices come in three families:
        (A) 8 vertices: permutations of (±1, 0, 0, 0)
        (B) 16 vertices: (±½, ±½, ±½, ±½)
        (C) 96 vertices: even permutations of (0, ±1/2, ±φ/2, ±1/(2φ))
        """
        verts = set()

        # (A) Permutations of (±1, 0, 0, 0)
        for i in range(4):
            for s in [1, -1]:
                v = [0, 0, 0, 0]
                v[i] = s
                verts.add(tuple(v))
        self.log(f"  Family A (axis-aligned): {len(verts)} vertices")

        # (B) All sign choices of (±½, ±½, ±½, ±½)
        n_before = len(verts)
        for s0 in [1, -1]:
            for s1 in [1, -1]:
                for s2 in [1, -1]:
                    for s3 in [1, -1]:
                        verts.add((s0*0.5, s1*0.5, s2*0.5, s3*0.5))
        self.log(f"  Family B (half-integer): {len(verts) - n_before} vertices")

        # (C) Even permutations of (0, ±1/2, ±φ/2, ±1/(2φ))
        n_before = len(verts)
        base = [0, 0.5, PHI/2, 1/(2*PHI)]
        # Even permutations of 4 elements (12 permutations)
        even_perms = self._even_permutations_4()
        for perm in even_perms:
            template = [base[p] for p in perm]
            # All sign choices for nonzero entries
            nonzero_idx = [i for i, x in enumerate(template) if abs(x) > 1e-10]
            for signs in range(2**len(nonzero_idx)):
                v = list(template)
                for k, idx in enumerate(nonzero_idx):
                    if signs & (1 << k):
                        v[idx] = -v[idx]
                verts.add(tuple(np.round(v, 10)))
        self.log(f"  Family C (golden): {len(verts) - n_before} vertices")

        verts = np.array(sorted(verts))
        # Verify all unit vectors
        norms = np.linalg.norm(verts, axis=1)
        self.check("All vertices are unit vectors",
                    np.allclose(norms, 1.0, atol=1e-10))
        self.log(f"  Total: {len(verts)} vertices")
        return verts

    def _even_permutations_4(self):
        """Return the 12 even permutations of (0,1,2,3)."""
        result = []
        for p in permutations(range(4)):
            # Count inversions to determine parity
            inv = sum(1 for i in range(4) for j in range(i+1, 4) if p[i] > p[j])
            if inv % 2 == 0:
                result.append(p)
        return result

    # ── Part 2: Vertex shells ───────────────────────────────────
    def analyze_vertex_shells(self, verts):
        """Shell structure from a reference vertex (inner product classes)."""
        ref = verts[0]
        dots = verts @ ref
        # Round to avoid floating point noise
        dots_rounded = np.round(dots, 8)
        unique_dots = np.sort(np.unique(dots_rounded))[::-1]

        self.log(f"  Reference vertex: {ref}")
        self.log(f"  {len(unique_dots)} distinct inner products:")

        cumulative = 0
        shells = []
        for d in unique_dots:
            count = np.sum(np.abs(dots_rounded - d) < 1e-7)
            cumulative += count
            shells.append((d, count, cumulative))
            self.log(f"    cos θ = {d:+.6f}  →  {count:3d} vertices"
                      f"  (cumul: {cumulative})")

        self.log(f"\n  Shell sizes: {[s[1] for s in shells]}")
        self.log(f"  Cumulative:  {[s[2] for s in shells]}")

        # With ×2 spin
        cum_spin = [2*s[2] for s in shells]
        self.log(f"  Cumul ×2 (spin): {cum_spin}")

        # Check magic number matches
        for m in MAGIC_NUMBERS:
            match = m in cum_spin or m in [s[2] for s in shells]
            if match:
                self.log(f"  ★ Magic {m} found in cumulative counts!")
        return shells

    # ── Part 3: Adjacency spectrum ──────────────────────────────
    def analyze_adjacency(self, verts):
        """Build adjacency matrix (nearest neighbors) and find eigenvalues."""
        N = len(verts)
        G = verts @ verts.T  # Gram matrix (inner products)
        G_round = np.round(G, 8)

        # Nearest neighbors: cos θ = φ/2 ≈ 0.809
        nn_threshold = PHI / 2 - 0.01
        adj = (G_round > nn_threshold) & (~np.eye(N, dtype=bool))
        degree = adj.sum(axis=1)
        self.log(f"  Coordination number: {int(degree[0])} (expect 12)")
        self.check("Coordination number = 12", int(degree[0]) == 12)

        # Eigenvalues of adjacency matrix
        A = adj.astype(float)
        eigvals = np.sort(np.linalg.eigvalsh(A))[::-1]
        unique_eigs = np.round(np.unique(np.round(eigvals, 4)), 4)
        self.log(f"  {len(unique_eigs)} distinct eigenvalues:")
        for e in sorted(unique_eigs, reverse=True):
            mult = np.sum(np.abs(eigvals - e) < 0.01)
            self.log(f"    λ = {e:+8.4f}  (mult {mult})")

        # Spectral gaps
        sorted_unique = np.sort(unique_eigs)[::-1]
        if len(sorted_unique) > 1:
            gaps = np.diff(-sorted_unique)
            max_gap_idx = np.argmax(gaps)
            self.log(f"\n  Largest spectral gap: between λ={sorted_unique[max_gap_idx]:.4f}"
                      f" and λ={sorted_unique[max_gap_idx+1]:.4f}"
                      f" (Δ={gaps[max_gap_idx]:.4f})")

    # ── Part 4: Tetrahedral cell shells ─────────────────────────
    def analyze_cell_shells(self, verts):
        """Build tetrahedral cells and analyze cell-shell structure."""
        N = len(verts)
        G = np.round(verts @ verts.T, 8)
        nn_cos = round(PHI / 2, 8)

        # Find edges (nearest neighbor pairs)
        edges = []
        for i in range(N):
            for j in range(i+1, N):
                if abs(G[i, j] - nn_cos) < 0.01:
                    edges.append((i, j))
        self.log(f"  Edges: {len(edges)} (expect 720)")
        self.check("720 edges", len(edges) == 720)

        # Build adjacency list
        adj = {i: set() for i in range(N)}
        for i, j in edges:
            adj[i].add(j)
            adj[j].add(i)

        # Find triangular faces: common neighbors of edge endpoints
        faces = set()
        for i, j in edges:
            common = adj[i] & adj[j]
            for k in common:
                face = tuple(sorted([i, j, k]))
                faces.add(face)
        self.log(f"  Faces: {len(faces)} (expect 1200)")
        self.check("1200 faces", len(faces) == 1200)

        # Find tetrahedra: common neighbors of face vertices
        cells = set()
        for f in faces:
            i, j, k = f
            common = adj[i] & adj[j] & adj[k]
            for l in common:
                cell = tuple(sorted([i, j, k, l]))
                cells.add(cell)
        self.log(f"  Cells: {len(cells)} (expect 600)")
        self.check("600 tetrahedral cells", len(cells) == 600)

        # Cell shells from reference vertex (vertex 0)
        # Count cells at distance 0, 1, 2, ... from vertex 0
        # Distance = minimum number of cell-adjacency steps
        cell_list = list(cells)
        v0_cells = [c for c in cell_list if 0 in c]
        self.log(f"  Cells containing vertex 0: {len(v0_cells)} (expect 20)")
        self.check("20 cells per vertex", len(v0_cells) == 20)

        # Vertices reachable by BFS through cell adjacency from vertex 0
        visited_verts = {0}
        frontier = set()
        for c in v0_cells:
            frontier.update(c)
        frontier -= visited_verts
        layer = 0
        self.log(f"\n  Cell-BFS vertex layers from vertex 0:")
        self.log(f"    Layer {layer}: {len(visited_verts)} verts (cumul: {len(visited_verts)})")
        while frontier:
            layer += 1
            visited_verts.update(frontier)
            self.log(f"    Layer {layer}: {len(frontier)} verts (cumul: {len(visited_verts)})")
            next_frontier = set()
            for v in frontier:
                for c in cell_list:
                    if v in c:
                        next_frontier.update(c)
            next_frontier -= visited_verts
            frontier = next_frontier

    # ── Part 5: Sub-shell decomposition ─────────────────────────
    def analyze_subshells(self, verts):
        """Decompose each distance shell using 3D projection + angular momentum.

        Project 4D vertices onto 3D (drop one coordinate) and analyze
        the angular momentum content of each shell.
        """
        ref = verts[0]
        dots = np.round(verts @ ref, 8)
        unique_dots = np.sort(np.unique(dots))[::-1]

        self.log("  Shell → 3D projection → angular momentum decomposition:")
        all_subshells = []

        for d in unique_dots:
            mask = np.abs(dots - d) < 1e-7
            shell_verts = verts[mask]
            n_shell = len(shell_verts)
            if n_shell <= 1:
                all_subshells.append((d, n_shell, [n_shell]))
                continue

            # Project to 3D: use last 3 coordinates, normalize
            proj = shell_verts[:, 1:]  # drop first coordinate
            norms = np.linalg.norm(proj, axis=1)
            # Some may project to zero — handle carefully
            nonzero = norms > 1e-10
            if nonzero.sum() < 2:
                all_subshells.append((d, n_shell, [n_shell]))
                continue
            proj_n = proj[nonzero] / norms[nonzero, None]

            # Compute multipole moments: ∑ Y_l^m(θ,φ)
            # Use Gram matrix eigenvalues to detect angular momentum content
            G3 = proj_n @ proj_n.T
            eigs = np.sort(np.linalg.eigvalsh(G3))[::-1]
            # Number of significant eigenvalues ≈ number of independent directions
            n_sig = np.sum(eigs > 0.1 * eigs[0])

            # Alternative: cluster by 3D dot products to find sub-shells
            dots3 = np.round(proj_n @ proj_n.T, 6)
            # Unique rows → orbits
            _, indices = np.unique(np.round(dots3, 4), axis=0, return_inverse=True)
            n_orbits = len(np.unique(indices))

            all_subshells.append((d, n_shell, n_orbits))
            self.log(f"    cos θ = {d:+.6f}: {n_shell:3d} verts, "
                      f"{n_sig} significant eigenvalues, "
                      f"{n_orbits} 3D-orbits")

    # ── Part 6: DRLT magic number search ────────────────────────
    def magic_number_search(self, verts):
        """Search for cumulative vertex counts matching magic numbers.

        Key idea: 120 = d! = 5!.  The binary icosahedral group 2I ≅ SL(2,5)
        acts on these vertices.  Its conjugacy classes have sizes
        1, 1, 12, 12, 12, 12, 20, 20, 30.

        We also try: inscribed polytope decompositions.
        """
        self.log("  --- Conjugacy class approach ---")
        # 2I conjugacy class sizes (ordered by element order)
        cc_sizes = [1, 1, 20, 20, 12, 12, 12, 12, 30]
        self.log(f"  2I conjugacy class sizes: {cc_sizes}")
        cumul = np.cumsum(cc_sizes)
        self.log(f"  Cumulative: {list(cumul)}")
        cumul_spin = 2 * cumul
        self.log(f"  Cumulative ×2 (spin): {list(cumul_spin)}")

        for m in MAGIC_NUMBERS:
            if m in cumul_spin:
                self.log(f"  ★ Magic {m} matched (×2)!")
            elif m in cumul:
                self.log(f"  ★ Magic {m} matched (×1)!")

        # Try different orderings of conjugacy classes
        self.log("\n  --- Optimal ordering search ---")
        best_score = 0
        best_order = None
        from itertools import permutations as perms
        # 9! = 362880 — feasible
        for perm in perms(range(len(cc_sizes))):
            ordered = [cc_sizes[p] for p in perm]
            cum = list(np.cumsum(ordered))
            cum_s2 = [2*c for c in cum]
            score = sum(1 for m in MAGIC_NUMBERS if m in cum_s2)
            if score > best_score:
                best_score = score
                best_order = ordered
                best_cum = cum_s2

        self.log(f"  Best ordering (×2 spin): {best_order}")
        self.log(f"  Cumulative ×2: {best_cum}")
        self.log(f"  Magic numbers matched: {best_score}/{len(MAGIC_NUMBERS)}")
        matched = [m for m in MAGIC_NUMBERS if m in best_cum]
        self.log(f"  Matched: {matched}")

        # Also try ×1 (no spin doubling)
        best_score1 = 0
        best_order1 = None
        for perm in perms(range(len(cc_sizes))):
            ordered = [cc_sizes[p] for p in perm]
            cum = list(np.cumsum(ordered))
            score = sum(1 for m in MAGIC_NUMBERS if m in cum)
            if score > best_score1:
                best_score1 = score
                best_order1 = ordered
                best_cum1 = cum

        self.log(f"\n  Best ordering (×1): {best_order1}")
        self.log(f"  Cumulative ×1: {best_cum1}")
        self.log(f"  Magic numbers matched: {best_score1}/{len(MAGIC_NUMBERS)}")
        matched1 = [m for m in MAGIC_NUMBERS if m in best_cum1]
        self.log(f"  Matched: {matched1}")

        # Key DRLT numbers
        self.log("\n  --- DRLT dimension connections ---")
        d = 5
        self.log(f"  d = {d}")
        from math import factorial
        self.log(f"  d! = {factorial(d)} = 120 (600-cell vertices)")
        self.log(f"  d!/d = {factorial(d)//d} = 24 (24-cell vertices)")
        self.log(f"  C(d+1,2) = {(d+1)*d//2} = 15")
        self.log(f"  2d = {2*d} = 10 (d-orthoplex vertices)")
        self.log(f"  2^d = {2**d} = 32 (d-cube vertices)")

        # 5 inscribed 24-cells
        self.log("\n  --- Inscribed 24-cells ---")
        self.log(f"  The 600-cell contains 5 inscribed 24-cells")
        self.log(f"  Each 24-cell has 24 vertices, total 5×24 = 120")
        self.log(f"  Filling by 24-cells: 24, 48, 72, 96, 120")
        self.log(f"  ×2 spin: 48, 96, 144, 192, 240")

        self.check(f"Best conjugacy ordering matches ≥ 3 magic numbers",
                    max(best_score, best_score1) >= 3)


if __name__ == "__main__":
    NUC001().execute()
