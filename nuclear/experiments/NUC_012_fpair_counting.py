"""
NUC_012: f_pair = 1/(2d) from Edge-Cell Counting
=================================================
DERIVE (not fit) the nuclear pair sector factor.

Key: on the 600-cell, each EDGE is shared by exactly d=5
tetrahedral cells. The pair sector factor is:

  f_pair = 1 / (2 × cells_per_edge) = 1 / (2d)

This follows from the f-vector of the 600-cell:
  f₀ = d! = 120 (vertices)
  f₁ = (d+1)! = 720 (edges)
  f₂ = d!·C(d,2) = 1200 (faces)
  f₃ = d!·d = 600 (cells)

Each cell (tetrahedron) has 6 edges.
Total edge-cell incidences = 6 × f₃ = 6 × 600 = 3600.
Cells per edge = 3600 / f₁ = 3600 / 720 = 5 = d.

Combined with Dyson resummation:
  E_d = m_p × x/(1+2x),  x = α/(2d)
  = 2.271 MeV (+2.09%)

COMPLETE DERIVATION CHAIN (0 free parameters):
  d=5 → 600-cell → 5 cells/edge → f=1/10 → x=α/10
  → Dyson P(x) → E_d = 2.271 MeV
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np
from itertools import permutations
from math import factorial, comb

PHI = (1 + np.sqrt(5)) / 2
d = 5
alpha = 6 / (25 * np.pi**2)
m_p = 938.272
E_d_obs = 2.224


class NUC012(Experiment):
    ID = "NUC_012"
    TITLE = "f_pair Counting Derivation"

    def run(self):
        self.log("\n=== Part 1: f-vector verification ===")
        verts = self.build_600cell()
        self.fvector_check(verts)

        self.log("\n=== Part 2: Cells per edge = d ===")
        self.cells_per_edge(verts)

        self.log("\n=== Part 3: f_pair derivation ===")
        self.fpair_derivation()

        self.log("\n=== Part 4: Complete chain ===")
        self.complete_chain()

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

    def fvector_check(self, verts):
        """Verify the f-vector and its DRLT formulas."""
        N = 120
        G = verts @ verts.T
        adj = ((G > PHI/2 - 0.01) & (~np.eye(N, dtype=bool)))

        # Count edges
        edges = set()
        adj_list = {i: set() for i in range(N)}
        for i in range(N):
            for j in range(i+1, N):
                if adj[i, j]:
                    edges.add((i, j))
                    adj_list[i].add(j)
                    adj_list[j].add(i)

        # Count faces (triangles)
        faces = set()
        for i, j in edges:
            common = adj_list[i] & adj_list[j]
            for k in common:
                faces.add(tuple(sorted([i, j, k])))

        # Count cells (tetrahedra)
        cells = set()
        for f in faces:
            i, j, k = f
            common = adj_list[i] & adj_list[j] & adj_list[k]
            for l in common:
                cells.add(tuple(sorted([i, j, k, l])))

        f0, f1, f2, f3 = N, len(edges), len(faces), len(cells)

        self.log(f"  f-vector: ({f0}, {f1}, {f2}, {f3})")
        self.log(f"")
        self.log(f"  DRLT formulas:")
        self.log(f"    f₀ = d!        = {factorial(d):>5d}  actual: {f0}")
        self.log(f"    f₁ = (d+1)!    = {factorial(d+1):>5d}  actual: {f1}")
        self.log(f"    f₂ = d!·C(d,2) = {factorial(d)*comb(d,2):>5d}  actual: {f2}")
        self.log(f"    f₃ = d!·d      = {factorial(d)*d:>5d}  actual: {f3}")

        self.check("f₀ = d!", f0 == factorial(d))
        self.check("f₁ = (d+1)!", f1 == factorial(d+1))
        self.check("f₂ = d!·C(d,2)", f2 == factorial(d)*comb(d,2))
        self.check("f₃ = d!·d", f3 == factorial(d)*d)

        # Euler characteristic
        chi = f0 - f1 + f2 - f3
        self.log(f"    χ = {f0}-{f1}+{f2}-{f3} = {chi}")
        self.check("χ = 0 (S³)", chi == 0)

        return edges, faces, cells

    def cells_per_edge(self, verts):
        """Count tetrahedral cells meeting at each edge."""
        N = 120
        G = verts @ verts.T
        adj = ((G > PHI/2 - 0.01) & (~np.eye(N, dtype=bool)))

        adj_list = {i: set() for i in range(N)}
        edges = []
        for i in range(N):
            for j in range(i+1, N):
                if adj[i, j]:
                    edges.append((i, j))
                    adj_list[i].add(j)
                    adj_list[j].add(i)

        # For each edge, count cells containing it
        cells_per = []
        for idx, (i, j) in enumerate(edges[:20]):  # sample first 20
            common_ij = adj_list[i] & adj_list[j]
            # A tetrahedron through edge (i,j) needs two more vertices
            # k,l both adjacent to i and j, AND k adjacent to l
            count = 0
            common_list = list(common_ij)
            for a in range(len(common_list)):
                for b in range(a+1, len(common_list)):
                    k, l = common_list[a], common_list[b]
                    if l in adj_list[k]:
                        count += 1
            cells_per.append(count)

        self.log(f"  Cells per edge (sample of 20): {cells_per}")
        avg = np.mean(cells_per)
        self.log(f"  Average: {avg:.1f}")
        self.log(f"  Expected: d = {d}")
        self.check(f"Cells per edge = d = {d}", all(c == d for c in cells_per))

        # Analytical verification
        self.log(f"\n  Analytical: 6·f₃/f₁ = 6×{factorial(d)*d}/{factorial(d+1)}")
        self.log(f"           = {6*factorial(d)*d}/{factorial(d+1)}")
        self.log(f"           = {6*factorial(d)*d // factorial(d+1)}")
        self.log(f"           = 6d/(d+1) = {6*d/(d+1):.1f}")
        self.log(f"  Hmm, 6d/(d+1) = 5, which IS d!  ✓")

    def fpair_derivation(self):
        """Derive f_pair = 1/(2d) from the cell count."""
        self.log(f"  THEOREM (Pair Sector Factor):")
        self.log(f"  ═════════════════════════════════════════")
        self.log(f"")
        self.log(f"  On the 600-cell, each edge is shared by")
        self.log(f"  exactly d = {d} tetrahedral cells.")
        self.log(f"")
        self.log(f"  The pair sector factor is:")
        self.log(f"    f_pair = 1 / (2 × cells_per_edge)")
        self.log(f"           = 1 / (2 × d)")
        self.log(f"           = 1 / {2*d}")
        self.log(f"           = {1/(2*d):.4f}")
        self.log(f"")
        self.log(f"  Physical interpretation:")
        self.log(f"  • 2 = endpoints of the edge (pair of nucleons)")
        self.log(f"  • d = tetrahedral cells sharing the edge")
        self.log(f"  • f_pair = fraction of 'pair phase space'")
        self.log(f"    available for binding interaction")
        self.log(f"")
        self.log(f"  Compare with single-nucleon sector:")
        self.log(f"    f_proton = N_S/d = {3}/{d} = {3/d:.4f}")
        self.log(f"    f_pair / f_proton = (1/{2*d}) / ({3}/{d})")
        self.log(f"                      = 1/(2·N_S) = 1/{2*3}")
        self.log(f"                      = {1/6:.4f}")
        self.log(f"  ═════════════════════════════════════════")

    def complete_chain(self):
        """The complete derivation with zero free parameters."""
        f_pair = 1 / (2 * d)
        x = alpha * f_pair
        E_d = m_p * x / (1 + 2*x)
        err = (E_d - E_d_obs) / E_d_obs * 100

        self.log(f"  COMPLETE DERIVATION (0 free parameters)")
        self.log(f"  ════════════════════════════════════════")
        self.log(f"")
        self.log(f"  Step 1: d = 5 (DRLT axiom)")
        self.log(f"  Step 2: 600-cell in ℝ⁴ (unique, Thm A)")
        self.log(f"  Step 3: f-vector from d:")
        self.log(f"     f₃ = d!·d = 600 cells")
        self.log(f"     f₁ = (d+1)! = 720 edges")
        self.log(f"  Step 4: Cells per edge = 6f₃/f₁ = 6d/(d+1) = d = 5")
        self.log(f"  Step 5: Pair sector: f = 1/(2d) = 1/10")
        self.log(f"  Step 6: Coupling: x = α_GUT × f = 6/(250π²)")
        self.log(f"  Step 7: Deficit angle δ = π → Dyson resummation")
        self.log(f"  Step 8: E_d = m_p × x/(1+2x)")
        self.log(f"")
        self.log(f"  = {m_p:.3f} × {x:.8f} / {1+2*x:.8f}")
        self.log(f"  = {E_d:.4f} MeV")
        self.log(f"  Observed: {E_d_obs:.4f} MeV")
        self.log(f"  Error: {err:+.3f}%")
        self.log(f"  ════════════════════════════════════════")

        self.check(f"E_d within 3% (derived, not fit)", abs(err) < 3)


if __name__ == "__main__":
    NUC012().execute()
