"""
NUC_015: Surface Coefficient from Gram Geometry
================================================
The surface coefficient a_S = 9.1 MeV is 46% below observed 16.8.

Diagnosis: NUC_010 used a_S = (d-1) × E_edge which only counts
"missing neighbors". But in the Gram approach (NUC_014), the
binding per neighbor is E_edge × G², not just E_edge.

The surface nucleon has BOTH:
  (a) Fewer neighbors (geometric: missing edges)
  (b) Different Gram overlaps (those present have VARIED G values)

The atoms lesson: screening depends on WHICH shells are occupied,
not just how many electrons are present.

For nuclei: the surface term depends on the GRAM STRUCTURE of
the boundary, not just the count of missing neighbors.

Method:
  1. Build caps of various sizes on the 600-cell
  2. For each cap size A, compute exact surface energy
  3. Fit A^{2/3} coefficient → a_S from geometry
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np
from itertools import permutations

PHI = (1 + np.sqrt(5)) / 2
d = 5
alpha = 6 / (25 * np.pi**2)
m_p = 938.272
E_edge = m_p * alpha / (2 * d)  # 2.282 MeV
G_nn = PHI / 2  # nearest neighbor Gram overlap


class NUC015(Experiment):
    ID = "NUC_015"
    TITLE = "Surface from Gram Geometry"

    def run(self):
        verts = self.build_600cell()
        adj = self.build_adj(verts)
        G = verts @ verts.T

        self.log("\n=== Part 1: Exact surface energy for each A ===")
        results = self.surface_scan(verts, adj, G)

        self.log("\n=== Part 2: Extract a_V, a_S from fit ===")
        self.extract_coefficients(results)

        self.log("\n=== Part 3: Gram-weighted surface ===")
        self.gram_surface(verts, adj, G)

    def build_600cell(self):
        verts = set()
        for i in range(4):
            for s in [1, -1]:
                v = [0]*4; v[i] = s; verts.add(tuple(v))
        for s0 in [1,-1]:
            for s1 in [1,-1]:
                for s2 in [1,-1]:
                    for s3 in [1,-1]:
                        verts.add((s0*.5, s1*.5, s2*.5, s3*.5))
        base = [0, 0.5, PHI/2, 1/(2*PHI)]
        for p in permutations(range(4)):
            inv = sum(1 for i in range(4) for j in range(i+1,4) if p[i]>p[j])
            if inv % 2 != 0: continue
            t = [base[p[k]] for k in range(4)]
            nz = [i for i,x in enumerate(t) if abs(x) > 1e-10]
            for signs in range(2**len(nz)):
                v = list(t)
                for k,idx in enumerate(nz):
                    if signs & (1<<k): v[idx] = -v[idx]
                verts.add(tuple(np.round(v, 10)))
        return np.array(sorted(verts))

    def build_adj(self, verts):
        G = verts @ verts.T
        return ((G > PHI/2 - 0.01) & (~np.eye(120, dtype=bool))).astype(float)

    def surface_scan(self, verts, adj, G):
        """For each cap size A, compute exact binding energy.

        Build a cap by growing from a seed vertex (BFS).
        For each A, compute:
          B(A) = Σ_{edges inside cap} E_edge × G_ij²
          S(A) = number of boundary edges (one end in, one out)

        B/A should show the volume-surface pattern.
        """
        N = 120
        # BFS from vertex with highest 1st-coord (near "north pole")
        seed = np.argmax(verts[:, 0])

        # Grow cap by BFS
        filled = set()
        frontier = [seed]
        order = []

        # Priority: add vertex with most filled neighbors first
        while len(order) < N:
            if not frontier:
                # Find unfilled vertex with most filled neighbors
                best = -1; best_count = -1
                for v in range(N):
                    if v not in filled:
                        c = sum(1 for u in filled if adj[v, u] > 0.5)
                        if c > best_count:
                            best_count = c; best = v
                frontier = [best]

            # Among frontier, pick the one with most filled neighbors
            best_v = max(frontier,
                         key=lambda v: sum(1 for u in filled if adj[v, u] > 0.5))
            frontier.remove(best_v)
            if best_v in filled:
                continue

            filled.add(best_v)
            order.append(best_v)

            # Add new neighbors to frontier
            for u in range(N):
                if adj[best_v, u] > 0.5 and u not in filled:
                    if u not in frontier:
                        frontier.append(u)

        # Compute binding for each cap size
        results = []
        self.log(f"  {'A':>4s}  {'B_total':>8s}  {'B/A':>8s}  "
                  f"{'interior':>8s}  {'boundary':>8s}  {'surf/vol':>8s}")

        for A in [2, 4, 8, 12, 16, 20, 28, 40, 56, 70, 82, 90, 100, 110, 120]:
            cap = set(order[:A])

            # Count edge types
            interior_edges = 0  # both ends in cap
            boundary_edges = 0  # one end in, one out
            B_gram = 0.0

            for i in cap:
                for j in range(N):
                    if adj[i, j] < 0.5:
                        continue
                    if j in cap and j > i:
                        interior_edges += 1
                        B_gram += G[i, j]**2
                    elif j not in cap:
                        boundary_edges += 1

            # Binding energy (Gram² model from NUC_014)
            B_total = E_edge * B_gram
            ba = B_total / A if A > 0 else 0

            sv = boundary_edges / max(interior_edges, 1)
            results.append((A, B_total, ba, interior_edges, boundary_edges))
            self.log(f"  {A:4d}  {B_total:8.2f}  {ba:8.3f}  "
                      f"{interior_edges:8d}  {boundary_edges:8d}  {sv:8.3f}")

        return results

    def extract_coefficients(self, results):
        """Fit B/A = a_V - a_S A^{-1/3} to extract coefficients."""
        As = np.array([r[0] for r in results if r[0] >= 12])
        BAs = np.array([r[2] for r in results if r[0] >= 12])

        # Linear fit: B/A = a_V - a_S × A^{-1/3}
        x = As**(-1/3)
        # B/A = a_V - a_S × x → linear in x
        # Least squares: [1, -x] @ [a_V, a_S]^T = B/A
        M = np.column_stack([np.ones_like(x), -x])
        coeffs, _, _, _ = np.linalg.lstsq(M, BAs, rcond=None)
        a_V_fit, a_S_fit = coeffs

        self.log(f"  Fit: B/A = a_V - a_S × A^(-1/3)")
        self.log(f"  a_V = {a_V_fit:.3f} MeV  (obs: ~15.5, NUC_010: 13.7)")
        self.log(f"  a_S = {a_S_fit:.3f} MeV  (obs: ~16.8, NUC_010: 9.1)")
        self.log(f"")

        err_V = (a_V_fit - 15.5) / 15.5 * 100
        err_S = (a_S_fit - 16.8) / 16.8 * 100
        self.log(f"  a_V error: {err_V:+.1f}%")
        self.log(f"  a_S error: {err_S:+.1f}%")
        self.check(f"a_S within 30% of observed", abs(err_S) < 30)

    def gram_surface(self, verts, adj, G):
        """Gram-weighted surface analysis.

        The surface energy = Σ_{boundary edges} E_edge × G_ij² × factor

        For the volume-surface decomposition:
        Volume: each interior edge contributes E_edge × G_nn²
        Surface: boundary edges are MISSING → energy deficit

        The surface coefficient is determined by:
          a_S = (avg boundary edges per surface nucleon) × E_edge × G_nn²

        On the 600-cell, a surface nucleon has:
          - 12 total neighbors (coordination)
          - k_filled neighbors inside the cap
          - (12-k_filled) missing neighbors

        The average number of missing neighbors depends on cap geometry.
        """
        N = 120
        seed = np.argmax(verts[:, 0])

        # Build optimal cap (same BFS as above)
        filled = set(); frontier = [seed]; order = []
        while len(order) < N:
            if not frontier:
                best = -1; best_count = -1
                for v in range(N):
                    if v not in filled:
                        c = sum(1 for u in filled if adj[v,u]>0.5)
                        if c > best_count: best_count = c; best = v
                frontier = [best]
            best_v = max(frontier,
                         key=lambda v: sum(1 for u in filled if adj[v,u]>0.5))
            frontier.remove(best_v)
            if best_v in filled: continue
            filled.add(best_v); order.append(best_v)
            for u in range(N):
                if adj[best_v,u]>0.5 and u not in filled and u not in frontier:
                    frontier.append(u)

        # Analyze surface structure at A=56 (near iron peak)
        A = 56
        cap = set(order[:A])

        surface_nucleons = []
        interior_nucleons = []
        for i in cap:
            n_filled = sum(1 for j in cap if adj[i,j] > 0.5)
            n_total = int(sum(adj[i]))
            if n_filled < n_total:
                surface_nucleons.append((i, n_filled, n_total - n_filled))
            else:
                interior_nucleons.append((i, n_filled))

        n_surf = len(surface_nucleons)
        n_int = len(interior_nucleons)
        avg_missing = np.mean([s[2] for s in surface_nucleons]) if surface_nucleons else 0
        avg_filled_surf = np.mean([s[1] for s in surface_nucleons]) if surface_nucleons else 0

        self.log(f"  Cap A={A}: {n_int} interior + {n_surf} surface nucleons")
        self.log(f"  Interior: all 12 neighbors filled")
        self.log(f"  Surface: avg {avg_filled_surf:.1f} filled, "
                  f"{avg_missing:.1f} missing")
        self.log(f"")

        # Surface energy = missing Gram² binding
        E_surf_per = avg_missing * E_edge * G_nn**2
        self.log(f"  Surface energy/nucleon = {avg_missing:.1f} × {E_edge:.3f} "
                  f"× {G_nn**2:.4f} = {E_surf_per:.3f} MeV")

        # The A^{2/3} coefficient
        a_S_gram = E_surf_per * A / A**(2/3) if n_surf > 0 else 0
        # Actually: a_S = (total surface energy) / A^{2/3}
        total_surf_E = sum(s[2] for s in surface_nucleons) * E_edge * G_nn**2
        a_S_gram2 = total_surf_E / A**(2/3)

        self.log(f"  Total surface energy: {total_surf_E:.2f} MeV")
        self.log(f"  a_S = surface_E / A^(2/3) = {a_S_gram2:.2f} MeV")
        self.log(f"  Observed: 16.8 MeV")
        err = (a_S_gram2 - 16.8) / 16.8 * 100
        self.log(f"  Error: {err:+.1f}%")
        self.check(f"Gram a_S within 30% of observed", abs(err) < 30)


if __name__ == "__main__":
    NUC015().execute()
