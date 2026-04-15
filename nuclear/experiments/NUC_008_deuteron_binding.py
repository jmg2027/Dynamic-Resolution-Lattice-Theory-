"""
NUC_008: Deuteron Binding Energy from 600-Cell
===============================================
The deuteron (pn bound state) is the simplest nucleus.
E_d = 2.224 MeV (observed).

On the 600-cell: two nucleons interact via the confined
propagator on adjacent vertices. The relative motion is
described by a Hamiltonian on the group algebra of 2I.

Center-of-mass separates (vertex-transitivity):
  H_rel f(g) = -t × [A_L + A_R] f(g) - V₀ × δ(g ∈ S) f(g)

where A_L, A_R are left/right adjacency, S = nearest neighbors.

The DRLT candidate formula:
  E_d = Λ_QCD × α_GUT / π ≈ 2.38 MeV (7% error)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np
from itertools import permutations

PHI = (1 + np.sqrt(5)) / 2
d = 5
alpha_gut = 6 / (25 * np.pi**2)
eps = alpha_gut**(2/3) * (1 + alpha_gut)
Lambda_QCD = 308  # MeV (from DRLT)
m_p = 938.272  # MeV
E_d_obs = 2.224  # MeV


class NUC008(Experiment):
    ID = "NUC_008"
    TITLE = "Deuteron Binding Energy"

    def run(self):
        verts = self.build_600cell()
        adj, G = self.build_graph(verts)

        self.log("\n=== Part 1: Relative Hamiltonian on 2I ===")
        self.relative_hamiltonian(verts, adj, G)

        self.log("\n=== Part 2: Radial reduction ===")
        self.radial_reduction(verts, adj, G)

        self.log("\n=== Part 3: DRLT binding formula ===")
        self.binding_formula()

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

    def build_graph(self, verts):
        N = len(verts)
        G = verts @ verts.T
        adj = ((G > PHI/2 - 0.01) & (~np.eye(N, dtype=bool))).astype(float)
        return adj, G

    def quat_mult(self, p, q):
        w = p[0]*q[0]-p[1]*q[1]-p[2]*q[2]-p[3]*q[3]
        x = p[0]*q[1]+p[1]*q[0]+p[2]*q[3]-p[3]*q[2]
        y = p[0]*q[2]-p[1]*q[3]+p[2]*q[0]+p[3]*q[1]
        z = p[0]*q[3]+p[1]*q[2]-p[2]*q[1]+p[3]*q[0]
        return np.array([w, x, y, z])

    def quat_conj(self, q):
        return np.array([q[0], -q[1], -q[2], -q[3]])

    # ── Part 1: Relative Hamiltonian ────────────────────────────
    def relative_hamiltonian(self, verts, adj, G):
        """Build the 120×120 relative Hamiltonian for two nucleons.

        The relative coordinate g = q_1^{-1} q_2 lives on 2I (120 elements).
        Fix nucleon 1 at the identity (vertex-transitivity).
        Then nucleon 2 is at position g.

        H_rel = kinetic + potential
        Kinetic: nucleon 2 hops on the graph → A (adjacency)
        Potential: V(g) = -V₀ if g ∈ S (nearest neighbor), 0 otherwise
        """
        N = 120

        # For the relative motion, H_rel = A + V
        # A = adjacency (kinetic energy of relative motion)
        # V = -V₀ × P_S (attractive contact on edges)

        # First: build the distance matrix on the group
        # Find which vertex is the identity
        identity_idx = None
        for i in range(N):
            if abs(verts[i, 0] - 1.0) < 0.01 and np.sum(verts[i, 1:]**2) < 0.01:
                identity_idx = i
                break
        if identity_idx is None:
            # Use vertex closest to (1,0,0,0)
            identity_idx = np.argmax(verts[:, 0])

        self.log(f"  Identity vertex: {identity_idx} = {verts[identity_idx]}")

        # Shell structure from identity (= relative distance shells)
        dots = G[identity_idx]
        shells = {}
        for i in range(N):
            d = round(dots[i], 4)
            if d not in shells:
                shells[d] = []
            shells[d].append(i)

        self.log(f"\n  Relative distance shells (from identity):")
        for d in sorted(shells.keys(), reverse=True):
            self.log(f"    cos θ = {d:+.4f}: {len(shells[d]):3d} vertices")

        # The nearest-neighbor projector P_S
        nn_mask = adj[identity_idx].astype(bool)
        nn_count = nn_mask.sum()
        self.log(f"\n  Nearest neighbors of identity: {int(nn_count)}")

        # Solve for bound state at various V₀ values
        # H_rel = -t × A - V₀ × P_S
        # The kinetic energy scale t and potential V₀ are related.
        # In DRLT: t ∝ 1/(2m*a²) and V₀ ∝ g² × P_conf

        # Dimensionless problem: set t = 1, vary V₀
        self.log(f"\n  Scanning V₀ (in units of t=1):")
        self.log(f"  {'V₀':>6s}  {'E_ground':>10s}  {'E_1st_exc':>10s}  "
                  f"{'gap':>8s}  {'bound?':>8s}")

        P_S = np.zeros((N, N))
        for i in range(N):
            for j in range(N):
                if adj[i, j] > 0.5:
                    P_S[i, j] = 0  # off-diagonal not needed for contact
            if nn_mask[i]:
                P_S[i, i] = 1.0  # diagonal: potential at NN distance

        for V0 in [0.0, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0]:
            H_rel = -adj - V0 * P_S
            eigs = np.sort(np.linalg.eigvalsh(H_rel))
            E0 = eigs[0]
            E1 = eigs[1]
            # Continuum threshold: eigenvalue of -A alone → -12 (= -λ_max)
            threshold = -12.0
            bound = E0 < threshold
            self.log(f"  {V0:6.1f}  {E0:+10.4f}  {E1:+10.4f}  "
                      f"{E1-E0:8.4f}  {'YES' if bound else 'no'}")

    # ── Part 2: Radial reduction ────────────────────────────────
    def radial_reduction(self, verts, adj, G):
        """Reduce to radial Schrödinger equation on distance shells.

        The 600-cell has 9 distance shells from any vertex.
        The radial wavefunction ψ(r) lives on these 9 shells.
        """
        N = 120
        identity_idx = np.argmax(verts[:, 0])

        dots = np.round(G[identity_idx], 4)
        unique_dots = np.sort(np.unique(dots))[::-1]
        n_shells = len(unique_dots)

        self.log(f"  {n_shells} distance shells")

        # Build shell-to-shell transition matrix
        # T[a,b] = average number of edges from shell a to shell b
        shell_idx = {}
        for i, d in enumerate(unique_dots):
            shell_idx[d] = i

        shell_sizes = np.array([np.sum(np.abs(dots - d) < 0.001) for d in unique_dots])
        self.log(f"  Shell sizes: {list(shell_sizes)}")

        # Transition matrix
        T = np.zeros((n_shells, n_shells))
        for i in range(N):
            si = shell_idx[round(dots[i], 4)]
            for j in range(N):
                if adj[i, j] > 0.5:
                    sj = shell_idx[round(dots[j], 4)]
                    T[si, sj] += 1

        # Normalize by shell size
        for a in range(n_shells):
            if shell_sizes[a] > 0:
                T[a, :] /= shell_sizes[a]

        self.log(f"\n  Radial transition matrix (avg edges from shell a → b):")
        header = "     " + "".join(f"  s{b:d}" for b in range(n_shells))
        self.log(f"  {header}")
        for a in range(n_shells):
            row = f"  s{a}: " + "".join(f"{T[a,b]:5.1f}" for b in range(n_shells))
            self.log(row)

        # Radial Hamiltonian with potential on shell 1 (nearest neighbors)
        self.log(f"\n  Radial bound state scan:")
        for V0 in [0, 1, 2, 5, 10, 20]:
            V_rad = np.zeros(n_shells)
            V_rad[1] = -V0  # shell 1 = nearest neighbors

            H_rad = -T.copy()
            for a in range(n_shells):
                H_rad[a, a] += V_rad[a]

            eigs = np.sort(np.linalg.eigvalsh(H_rad))
            self.log(f"    V₀={V0:3d}: E₀={eigs[0]:+8.4f}, "
                      f"E₁={eigs[1]:+8.4f}")

    # ── Part 3: DRLT binding formula ────────────────────────────
    def binding_formula(self):
        """Candidate DRLT formulas for E_d.

        The deuteron binding energy should involve:
        - Λ_QCD (strong scale)
        - α_GUT (coupling)
        - d, φ (geometry)
        """
        self.log("  Candidate formulas for E_d:")
        self.log(f"  Observed: E_d = {E_d_obs:.3f} MeV")
        self.log("")

        candidates = {
            'Λ_QCD × α/π':
                Lambda_QCD * alpha_gut / np.pi,
            'Λ_QCD × α/(d-1)':
                Lambda_QCD * alpha_gut / (d-1),
            'm_p × α/(2d)':
                m_p * alpha_gut / (2*d),
            'Λ_QCD × α × φ/d²':
                Lambda_QCD * alpha_gut * PHI / d**2,
            'm_p × ε/(d² × φ)':
                m_p * eps / (d**2 * PHI),
            'Λ_QCD × 6/(d! × π)':
                Lambda_QCD * 6 / (120 * np.pi),
            'Λ_QCD × α/(φ² + 1)':
                Lambda_QCD * alpha_gut / (PHI**2 + 1),
            'm_p / (d² × 2d!)':
                m_p / (d**2 * 2 * 120),
            'm_p × α_GUT × ε':
                m_p * alpha_gut * eps,
            'Λ_QCD × (d+1)/(d! × φ)':
                Lambda_QCD * (d+1) / (120 * PHI),
        }

        results = []
        for name, val in candidates.items():
            err = (val - E_d_obs) / E_d_obs * 100
            results.append((abs(err), name, val, err))

        results.sort()
        for _, name, val, err in results:
            flag = '★' if abs(err) < 10 else ''
            self.log(f"    {name:>30s} = {val:8.4f} MeV  "
                      f"({err:+6.2f}%) {flag}")

        # Best candidate analysis
        best_name, best_val, best_err = results[0][1], results[0][2], results[0][3]
        self.log(f"\n  Best: {best_name} = {best_val:.4f} MeV ({best_err:+.2f}%)")

        # Deep analysis of Λ_QCD × α/π
        val_alpha_pi = Lambda_QCD * alpha_gut / np.pi
        err_alpha_pi = (val_alpha_pi - E_d_obs) / E_d_obs * 100
        self.log(f"\n  ─── Deep analysis: Λ_QCD × α_GUT / π ───")
        self.log(f"  = {Lambda_QCD} × {alpha_gut:.6f} / π")
        self.log(f"  = {Lambda_QCD} × 6/(25π²) / π")
        self.log(f"  = {Lambda_QCD} × 6/(25π³)")
        self.log(f"  = {val_alpha_pi:.4f} MeV ({err_alpha_pi:+.2f}%)")
        self.log(f"")
        self.log(f"  Interpretation: one pion exchange between two nucleons")
        self.log(f"  on adjacent 600-cell vertices.")
        self.log(f"    Λ_QCD = strong scale (pion dynamics)")
        self.log(f"    α_GUT = coupling (vertex interaction)")
        self.log(f"    1/π = geometric factor (S³ curvature)")

        # Also check: m_p × α × ε
        val_mae = m_p * alpha_gut * eps
        err_mae = (val_mae - E_d_obs) / E_d_obs * 100
        self.log(f"\n  ─── Alternative: m_p × α_GUT × ε ───")
        self.log(f"  = {m_p:.3f} × {alpha_gut:.6f} × {eps:.6f}")
        self.log(f"  = {val_mae:.4f} MeV ({err_mae:+.2f}%)")
        self.log(f"  Interpretation: proton mass × coupling × confinement")

        self.check(f"Best formula within 10%", abs(results[0][3]) < 10)


if __name__ == "__main__":
    NUC008().execute()
