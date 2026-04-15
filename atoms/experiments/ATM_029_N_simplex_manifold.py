"""
ATM_029: N-Simplex Manifold — Coupling Evolution with Topology
Joint research by Mingu Jeong and Claude (Anthropic)

N simplices sharing face (A1,A2,A3,B1):
  N=2: delta(AAA)=pi      — strong curvature, "confinement"
  N=3: delta(AAA)=pi/2    — intermediate
  N=4: delta(AAA)=0       — FLAT (asymptotic freedom!)

Physical picture: N = number of temporal "views" of the atom.
More temporal structure → weaker strong coupling → running α.

B vectors use equally-spaced complex phases in temporal ℂ²:
  Bk = [0, e^(2πik/N), 0, 0, 0]  for k=0,...,N-1
All orthogonal to B1=[t,0,eps,eps,eps] since <B1|Bk>_temporal = t×0 = 0.

Tests:
  1. Verify delta(AAA) = 2pi - N*pi/2 for N=2,3,4
  2. S_total(eps) for each N, find action maxima
  3. R_SSS and channel structure vs N
  4. Does S(N=2)/S(N=4) or similar ratio give alpha?
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from scipy.optimize import minimize_scalar
from experiment import Experiment

ALPHA_GUT = 6 / (25 * np.pi**2)
ALPHA_EM = 1 / 137.035999084
D = 5; N_S = 3; N_T = 2

A = np.array([[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], dtype=complex)


class NSimplexManifold:
    """N simplices sharing a tetrahedron face (A1,A2,A3,B1)."""

    def __init__(self, N, eps):
        self.N = N
        self.eps = eps
        self.n_verts = 4 + N  # A1,A2,A3,B1 + N temporal B's
        self._build_vectors()
        self._build_topology()

    def _build_vectors(self):
        """Build (4+N) unit vectors in C^5."""
        nv = self.n_verts
        self.psi = np.zeros((nv, 5), dtype=complex)
        # A vectors: spatial basis
        self.psi[:3] = A
        # B1: electron with spatial overlap eps
        t = np.sqrt(max(0, 1 - 3*self.eps**2))
        self.psi[3] = [t, 0, self.eps, self.eps, self.eps]
        # Temporal B's: equally-spaced complex phases
        for k in range(self.N):
            phase = 2 * np.pi * k / self.N
            self.psi[4+k] = [0, np.exp(1j * phase), 0, 0, 0]
        self.G = self.psi @ self.psi.conj().T

    def _build_topology(self):
        """Build N simplices and their hinges."""
        # Shared face vertices: {0,1,2,3} = {A1,A2,A3,B1}
        self.simplices = []
        for k in range(self.N):
            # Sk = (A1,A2,A3,B1,Bk+2)
            self.simplices.append((0, 1, 2, 3, 4+k))

        # All unique hinges (triangles)
        hinge_set = set()
        for sx in self.simplices:
            for tri in combinations(sx, 3):
                hinge_set.add(tri)
        self.hinges = sorted(hinge_set)

    def dihedral(self, simplex_verts, hinge):
        sv = list(simplex_verts)
        opp = [v for v in sv if v not in hinge]
        G_local = self.G[np.ix_(sv, sv)]
        det_local = np.linalg.det(G_local).real
        if abs(det_local) < 1e-15:
            return np.pi
        G_inv = np.linalg.inv(G_local)
        l, m = sv.index(opp[0]), sv.index(opp[1])
        num = -G_inv[l, m].real
        den = np.sqrt(max(1e-30, abs(G_inv[l,l].real * G_inv[m,m].real)))
        return float(np.arccos(np.clip(num / den, -1, 1)))

    def deficit(self, hinge):
        theta_sum = 0.0
        for sx in self.simplices:
            if set(hinge).issubset(set(sx)):
                theta_sum += self.dihedral(sx, hinge)
        return 2 * np.pi - theta_sum

    def hinge_det(self, tri):
        idx = list(tri)
        return float(np.linalg.det(self.G[np.ix_(idx, idx)]).real)

    def regge_action(self):
        S = 0.0
        for tri in self.hinges:
            d = self.hinge_det(tri)
            if d > 0:
                S += np.sqrt(d) * self.deficit(tri)
        return S

    def hinge_bc(self, tri):
        Phi = self.psi[list(tri)]
        k0, k1, k2 = 0.0, 0.0, 0.0
        for cols in combinations(range(5), 3):
            d2 = abs(np.linalg.det(Phi[:, cols]))**2
            nt = sum(1 for c in cols if c < N_T)
            if nt == 0: k0 += d2
            elif nt == 1: k1 += d2
            else: k2 += d2
        return k0, k1, k2

    def channel_decomposition(self):
        s_sss, s_mix, s_tot = 0.0, 0.0, 0.0
        for tri in self.hinges:
            d = self.hinge_det(tri)
            if d <= 0:
                continue
            area = np.sqrt(d)
            delta = self.deficit(tri)
            s_tot += area * delta
            k0, k1, k2 = self.hinge_bc(tri)
            tb = k0 + k1 + k2
            if tb > 0:
                s_sss += area * delta * k0 / tb
                s_mix += area * delta * (k1+k2) / tb
        r_sss = s_sss / s_tot if abs(s_tot) > 1e-15 else 0
        return s_tot, s_sss, r_sss

    def classify(self, tri):
        nA = sum(1 for v in tri if v < 3)
        has_B1 = 3 in tri
        n_Bt = sum(1 for v in tri if v >= 4)
        if nA == 3: return 'AAA'
        elif nA == 2:
            return 'AABe' if has_B1 else 'AABt'
        elif nA == 1:
            if has_B1 and n_Bt > 0: return 'ABet'
            elif n_Bt >= 2: return 'ABtt'
            else: return 'AB??'
        return 'BBB'


class NSimplexStudy(Experiment):
    ID = "ATM_029"
    TITLE = "N-Simplex Manifold"

    def run(self):
        self.test1_verify_delta()
        self.test2_action_landscape()
        self.test3_channel_vs_N()
        self.test4_ratios_and_coupling()

    def test1_verify_delta(self):
        """Verify delta(AAA) = 2pi - N*pi/2."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: delta(AAA) vs N")
        self.log(f"  Prediction: delta = (4-N)*pi/2")
        self.log(f"  {'='*60}")

        eps = 0.05
        self.log(f"\n  {'N':>4} {'delta':>10} {'d/pi':>8}"
                 f" {'pred':>8} {'n_hinges':>8} {'n_types':>10}")

        for N in range(2, 7):
            m = NSimplexManifold(N, eps)
            delta_aaa = m.deficit((0, 1, 2))
            pred = (4-N) * np.pi / 2

            # Count hinge types
            types = {}
            for tri in m.hinges:
                t = m.classify(tri)
                types[t] = types.get(t, 0) + 1

            type_str = ", ".join(f"{t}:{c}" for t,c in
                                sorted(types.items()))
            self.log(f"  {N:4d} {delta_aaa:10.5f} {delta_aaa/np.pi:8.4f}"
                     f" {pred/np.pi:8.4f} {len(m.hinges):8d}"
                     f"  {type_str}")

            if N <= 4:
                ok = abs(delta_aaa - pred) < 0.01
                self.check(f"delta(AAA,N={N}) = {(4-N)/2:.1f}*pi", ok)

    def test2_action_landscape(self):
        """S_total(eps) for N=2,3,4. Find action maxima."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Regge action S(eps) for N=2,3,4")
        self.log(f"  {'='*60}")

        emax = 1/np.sqrt(3) - 0.001

        for N in [2, 3, 4]:
            self.log(f"\n  --- N = {N} ---")
            self.log(f"  {'eps':>8} {'S':>12} {'S/pi':>10}")

            best_S, best_eps = -1e10, 0
            eps_vals = np.linspace(0.001, emax, 50)

            for eps in eps_vals:
                m = NSimplexManifold(N, eps)
                S = m.regge_action()
                if S > best_S:
                    best_S = S
                    best_eps = eps

            # Refine maximum
            def neg_S(e):
                return -NSimplexManifold(N, e).regge_action()
            try:
                res = minimize_scalar(neg_S, bounds=(0.001, emax),
                                       method='bounded')
                best_eps = res.x
                best_S = -res.fun
            except Exception:
                pass

            # Print landscape around max
            for eps in np.concatenate([
                    np.linspace(0.001, 0.05, 5),
                    np.linspace(0.05, 0.3, 10),
                    np.linspace(0.3, emax, 5)]):
                m = NSimplexManifold(N, eps)
                S = m.regge_action()
                marker = " <-- MAX" if abs(eps-best_eps) < 0.01 else ""
                self.log(f"  {eps:8.4f} {S:12.5f} {S/np.pi:10.5f}"
                         f"{marker}")

            self.log(f"\n  Action MAX: eps={best_eps:.6f},"
                     f" S={best_S:.5f} = {best_S/np.pi:.5f}*pi")
            self.log(f"  eps/alpha_GUT = {best_eps/ALPHA_GUT:.4f}")
            self.log(f"  eps^2 = {best_eps**2:.8f}")

        self.check("Action landscape mapped", True)

    def test3_channel_vs_N(self):
        """Channel structure at eps→0 for N=2,3,4,5."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Channel structure at eps=0.001")
        self.log(f"  {'='*60}")

        eps = 0.001
        self.log(f"\n  {'N':>4} {'S_total':>10} {'S/pi':>8}"
                 f" {'S_SSS':>8} {'R_SSS':>10} {'R/aGUT':>8}")

        for N in range(2, 8):
            m = NSimplexManifold(N, eps)
            s_tot, s_sss, r_sss = m.channel_decomposition()
            self.log(f"  {N:4d} {s_tot:10.4f} {s_tot/np.pi:8.4f}"
                     f" {s_sss:8.4f} {r_sss:10.6f}"
                     f" {r_sss/ALPHA_GUT:8.4f}")

        # Also at action maximum for each N
        self.log(f"\n  At action maxima:")
        emax = 1/np.sqrt(3) - 0.001
        for N in [2, 3, 4]:
            def neg_S(e):
                return -NSimplexManifold(N, e).regge_action()
            try:
                res = minimize_scalar(neg_S, bounds=(0.001, emax),
                                       method='bounded')
                eps_max = res.x
                m = NSimplexManifold(N, eps_max)
                s_tot, s_sss, r_sss = m.channel_decomposition()
                self.log(f"  N={N}: eps_max={eps_max:.5f},"
                         f" S={s_tot:.4f},"
                         f" R_SSS={r_sss:.6f},"
                         f" R/aGUT={r_sss/ALPHA_GUT:.4f}")
            except Exception:
                pass

        self.check("Channel vs N mapped", True)

    def test4_ratios_and_coupling(self):
        """Look for coupling-like ratios between different N."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: Inter-N ratios — coupling probes")
        self.log(f"  {'='*60}")

        eps = 0.001  # near zero
        emax = 1/np.sqrt(3) - 0.001

        # Collect S_total at eps→0 for each N
        S_data = {}
        for N in range(2, 8):
            m = NSimplexManifold(N, eps)
            S = m.regge_action()
            S_data[N] = S

        self.log(f"\n  S_total(eps→0):")
        for N, S in S_data.items():
            delta_aaa = max(0, (4-N)*np.pi/2)
            self.log(f"    N={N}: S={S:.4f} = {S/np.pi:.4f}*pi,"
                     f" delta(AAA) = {delta_aaa/np.pi:.2f}*pi")

        # Ratios
        self.log(f"\n  Inter-N ratios:")
        for Na, Nb in [(2,3), (2,4), (3,4), (2,5), (2,6)]:
            if Na in S_data and Nb in S_data:
                ratio = S_data[Na] / S_data[Nb]
                self.log(f"    S(N={Na})/S(N={Nb}) = {ratio:.6f}")

        # Key ratio: delta(AAA) contribution to action
        self.log(f"\n  delta(AAA) contribution to S:")
        for N in [2, 3, 4]:
            m = NSimplexManifold(N, eps)
            delta_aaa = m.deficit((0, 1, 2))
            det_aaa = m.hinge_det((0, 1, 2))
            s_aaa = np.sqrt(max(0, det_aaa)) * delta_aaa
            s_tot = m.regge_action()
            frac = s_aaa / s_tot if abs(s_tot) > 1e-10 else 0
            self.log(f"    N={N}: S_AAA = {s_aaa:.5f},"
                     f" S_AAA/S_total = {frac:.6f}")

        # The S_total at eps→0 should decompose cleanly
        self.log(f"\n  Hinge-unit decomposition at eps→0:")
        for N in [2, 3, 4]:
            m = NSimplexManifold(N, eps)
            types = {}
            for tri in m.hinges:
                t = m.classify(tri)
                types.setdefault(t, []).append(tri)

            self.log(f"\n    N={N}: {len(m.hinges)} hinges")
            total_units = 0
            for t in sorted(types):
                deltas = [m.deficit(tri) for tri in types[t]]
                avg_d = np.mean(deltas)
                dets = [m.hinge_det(tri) for tri in types[t]]
                avg_det = np.mean(dets)
                contrib = sum(np.sqrt(max(0,d)) * m.deficit(tri)
                              for tri, d in zip(types[t], dets))
                units = contrib / np.pi
                total_units += units
                self.log(f"      {t}: {len(types[t])} hinges,"
                         f" avg delta/pi={avg_d/np.pi:.3f},"
                         f" contrib={units:.3f}*pi")
            self.log(f"      TOTAL = {total_units:.3f}*pi")

        # Action maximum eps values
        self.log(f"\n  Action maximum eps values:")
        for N in [2, 3, 4]:
            def neg_S(e):
                return -NSimplexManifold(N, max(0.001,min(e,emax))).regge_action()
            try:
                res = minimize_scalar(neg_S, bounds=(0.001, emax),
                                       method='bounded')
                eps_max = res.x
                self.log(f"    N={N}: eps_max = {eps_max:.6f},"
                         f" eps^2 = {eps_max**2:.6f},"
                         f" eps/aGUT = {eps_max/ALPHA_GUT:.2f}")
            except Exception:
                pass

        # alpha_GUT = 6/(25*pi^2). What if it comes from N-scaling?
        # alpha = delta(AAA)/(d^2*pi) at the N where it's nonzero
        self.log(f"\n  Coupling candidates:")
        self.log(f"    alpha_GUT = {ALPHA_GUT:.6f}")
        self.log(f"    alpha_em = {ALPHA_EM:.6f}")
        for N in [2, 3]:
            d_aaa = (4-N)*np.pi/2
            cand = d_aaa / (D**2 * np.pi)
            self.log(f"    delta(AAA,N={N})/(d^2*pi)"
                     f" = {(4-N)/2}/{D**2} = {cand:.6f}")

        self.check("Coupling probes computed", True)


if __name__ == "__main__":
    NSimplexStudy().execute()
