"""
ATM_024: Variational on CORRECT Geometry — Δ⁴ (5 vertices)
Joint research by Mingu Jeong and Claude (Anthropic)

ATM_023 used WRONG geometry (6 vertices, ∂(Δ⁵)).
The correct object: 4-simplex Δ⁴ with 5 vertices.
  A₁,A₂,A₃ (spatial, fixed) + B₁,B₂ (temporal, variable)

Hinges: C(5,3) = 10 triangles
  AAA: 1  (strong force)
  AAB: 6  (EM/weak binding)
  ABB: 3  (electron-electron)
  BBB: 0  (impossible! only 2 B-vertices)

H  = B₁ occupied, B₂ vacant (temporal)
He = B₁ and B₂ both occupied (full simplex!)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from scipy.optimize import minimize
from itertools import combinations
from experiment import Experiment

ALPHA = 1 / 137.035999084
D = 5; N_S = 3; N_T = 2; Ry = 13.606

# Fixed A-vertices (spatial sector of C^5)
A = np.array([[0,0,1,0,0], [0,0,0,1,0], [0,0,0,0,1]],
             dtype=complex)
ALL_TRIS = list(combinations(range(5), 3))  # 10 hinges


def hinge_det(G, tri):
    idx = list(tri)
    return float(np.linalg.det(G[np.ix_(idx, idx)]).real)


def dihedral_at_triangle(G5, triangle):
    """Dihedral angle of Δ⁴ at triangular hinge.

    The two vertices NOT in the triangle define the
    opposite edge. The angle is between the two
    tetrahedra sharing this triangle.
    """
    all_v = set(range(5))
    opp = sorted(all_v - set(triangle))
    l, m = opp[0], opp[1]
    det_G = np.linalg.det(G5).real
    if abs(det_G) < 1e-15:
        return np.pi
    G_inv = np.linalg.inv(G5)
    num = -G_inv[l, m].real
    den = np.sqrt(max(1e-30,
                      abs(G_inv[l, l].real * G_inv[m, m].real)))
    return float(np.arccos(np.clip(num / den, -1, 1)))


def deficit_angle(G5, triangle):
    """δ_h = 2π - θ_h for single 4-simplex."""
    return 2 * np.pi - dihedral_at_triangle(G5, triangle)


def regge_action(G5):
    """S = Σ_h A_h × δ_h over 10 hinges of Δ⁴."""
    S = 0.0
    for tri in ALL_TRIS:
        d = hinge_det(G5, tri)
        if d > 0:
            S += np.sqrt(d) * deficit_angle(G5, tri)
    return S


def classify(tri):
    nA = sum(1 for v in tri if v < 3)
    return {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[nA]


def analyze(G5):
    """Full analysis of a Gram configuration."""
    r = {'S': regge_action(G5)}
    for label in ['AAA', 'AAB', 'ABB']:
        dets = [hinge_det(G5, t) for t in ALL_TRIS
                if classify(t) == label]
        r[label + '_det'] = dets
        r[label + '_avg'] = np.mean(dets) if dets else 0
    # Per-hinge details
    r['hinges'] = []
    for tri in ALL_TRIS:
        d = hinge_det(G5, tri)
        da = deficit_angle(G5, tri) if d > 0 else 0
        th = dihedral_at_triangle(G5, tri)
        r['hinges'].append({
            'tri': tri, 'type': classify(tri),
            'det': d, 'delta': da, 'theta': th
        })
    return r


# ── B-vertex construction ──

def make_config(eps1, phi1, eps2, phi2):
    """Build 5×5 Gram matrix for configuration.
    B₁ = [t₁cosφ₁, t₁sinφ₁, ε₁, ε₁, ε₁]
    B₂ = [t₂cosφ₂, t₂sinφ₂, ε₂, ε₂, ε₂]
    """
    psi = np.zeros((5, 5), dtype=complex)
    psi[:3] = A
    for i, (eps, phi) in enumerate([(eps1, phi1), (eps2, phi2)]):
        t = np.sqrt(max(0, 1 - 3 * eps**2))
        psi[3 + i] = [t * np.cos(phi), t * np.sin(phi),
                       eps, eps, eps]
    return psi @ psi.conj().T, psi


class CorrectGeometry(Experiment):
    ID = "ATM_024"
    TITLE = "Correct Geometry Variational"

    def run(self):
        self.test1_landscape_H()
        self.test2_optimize_H()
        self.test3_landscape_He()
        self.test4_optimize_He()
        self.test5_hinge_anatomy()

    def test1_landscape_H(self):
        """Scan S(ε) for hydrogen on Δ⁴."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: H landscape on Δ⁴ (B₂ vacant)")
        self.log(f"  {'='*60}")
        self.log(f"  B₁ = electron (ε₁ variable)")
        self.log(f"  B₂ = temporal [cosφ₂, sinφ₂, 0, 0, 0]")
        self.log(f"")
        self.log(f"  {'eps':>8} {'S':>10} {'AAA':>8} {'AAB_avg':>8}"
                 f" {'ABB_avg':>8}")
        eps_max = 1 / np.sqrt(3) - 0.001
        best_S, best_eps = -1e10, 0
        for eps in np.concatenate([
                np.linspace(0.001, 0.01, 10),
                np.linspace(0.01, 0.1, 20),
                np.linspace(0.1, eps_max, 20)]):
            G, _ = make_config(eps, 0.0, 0.0, np.pi/2)
            r = analyze(G)
            if r['S'] > best_S:
                best_S = r['S']
                best_eps = eps
            self.log(f"  {eps:8.5f} {r['S']:10.5f}"
                     f" {r['AAA_avg']:8.5f} {r['AAB_avg']:8.5f}"
                     f" {r['ABB_avg']:8.5f}")
        self.log(f"\n  S maximum at eps = {best_eps:.5f}, S = {best_S:.5f}")
        self.check("H landscape scanned", True)

    def test2_optimize_H(self):
        """Find all critical points for H on Δ⁴."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: H optimization on Δ⁴")
        self.log(f"  {'='*60}")
        eps_max = 1 / np.sqrt(3) - 0.001
        results = []
        # Sweep + optimize
        for eps0 in np.linspace(0.001, eps_max, 40):
            for sign in [-1, 1]:
                def obj(p, s=sign):
                    G, _ = make_config(abs(p[0]), p[1],
                                       0.0, np.pi/2)
                    return s * regge_action(G)
                try:
                    res = minimize(obj, [eps0, 0.0],
                                   method='L-BFGS-B',
                                   bounds=[(1e-4, eps_max),
                                           (0, 2*np.pi)],
                                   options={'maxiter': 3000})
                    G, psi = make_config(abs(res.x[0]), res.x[1],
                                         0.0, np.pi/2)
                    S = regge_action(G)
                    results.append((S, abs(res.x[0]), sign))
                except Exception:
                    pass

        # Cluster
        results.sort(key=lambda x: x[0], reverse=True)
        unique = [results[0]]
        for r in results[1:]:
            if all(abs(r[0] - u[0]) > 1e-4 for u in unique):
                unique.append(r)
        self.log(f"\n  Found {len(unique)} distinct critical points:")
        for i, (S, eps, sgn) in enumerate(unique[:10]):
            opt = "max" if sgn == -1 else "min"
            self.log(f"  #{i+1}: S={S:.6f}  eps={eps:.6f}"
                     f"  ({opt})")
        self.check("H critical points found", len(unique) > 0)

    def test3_landscape_He(self):
        """Scan S(ε₁,ε₂) for helium on Δ⁴."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: He landscape on Δ⁴ (both B occupied)")
        self.log(f"  {'='*60}")
        self.log(f"  B₁ = electron 1, B₂ = electron 2")
        self.log(f"  φ₁=0, φ₂=π/2 (orthogonal temporal)")
        self.log(f"")
        self.log(f"  {'eps1':>8} {'eps2':>8} {'S':>10}"
                 f" {'AAB_avg':>8} {'ABB_avg':>8}")
        eps_max = 1 / np.sqrt(3) - 0.001
        best_S, best_e = -1e10, (0, 0)
        for e1 in np.linspace(0.001, eps_max, 15):
            for e2 in np.linspace(0.001, e1, 10):
                G, _ = make_config(e1, 0.0, e2, np.pi/2)
                S = regge_action(G)
                if S > best_S:
                    best_S = S
                    best_e = (e1, e2)
        self.log(f"  Best: eps=({best_e[0]:.4f}, {best_e[1]:.4f})"
                 f"  S={best_S:.5f}")
        # Show slice at best e1
        e1_best = best_e[0]
        for e2 in np.linspace(0.001, eps_max, 20):
            G, _ = make_config(e1_best, 0.0, e2, np.pi/2)
            r = analyze(G)
            self.log(f"  {e1_best:8.4f} {e2:8.4f} {r['S']:10.5f}"
                     f" {r['AAB_avg']:8.5f} {r['ABB_avg']:8.5f}")
        self.check("He landscape scanned", True)

    def test4_optimize_He(self):
        """Find critical points for He on Δ⁴."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: He optimization on Δ⁴")
        self.log(f"  {'='*60}")
        eps_max = 1 / np.sqrt(3) - 0.001
        results = []
        for _ in range(200):
            e1 = np.random.uniform(0.001, eps_max)
            e2 = np.random.uniform(0.001, eps_max)
            ph1 = np.random.uniform(0, 2*np.pi)
            ph2 = np.random.uniform(0, 2*np.pi)
            for sign in [-1, 1]:
                def obj(p, s=sign):
                    G, _ = make_config(abs(p[0]), p[1],
                                       abs(p[2]), p[3])
                    return s * regge_action(G)
                try:
                    res = minimize(obj, [e1, ph1, e2, ph2],
                                   method='L-BFGS-B',
                                   bounds=[(1e-4,eps_max),(0,2*np.pi),
                                           (1e-4,eps_max),(0,2*np.pi)],
                                   options={'maxiter':3000})
                    G, psi = make_config(abs(res.x[0]), res.x[1],
                                         abs(res.x[2]), res.x[3])
                    S = regge_action(G)
                    eps = sorted([abs(res.x[0]), abs(res.x[2])],
                                 reverse=True)
                    results.append((S, eps, sign))
                except Exception:
                    pass

        results.sort(key=lambda x: x[0], reverse=True)
        unique = [results[0]]
        for r in results[1:]:
            if all(abs(r[0] - u[0]) > 1e-4 for u in unique):
                unique.append(r)
        self.log(f"\n  Found {len(unique)} distinct critical points:")
        for i, (S, eps, sgn) in enumerate(unique[:10]):
            opt = "max" if sgn == -1 else "min"
            self.log(f"  #{i+1}: S={S:.6f}  eps=[{eps[0]:.5f},"
                     f" {eps[1]:.5f}]  ({opt})")
        self.check("He critical points found", len(unique) > 0)

    def test5_hinge_anatomy(self):
        """Detailed hinge analysis at key configurations."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 5: Hinge anatomy")
        self.log(f"  {'='*60}")

        configs = [
            ("H (eps=0.004)", 0.004, 0.0, 0.0, np.pi/2),
            ("H (eps=0.1)",   0.1,   0.0, 0.0, np.pi/2),
            ("He (eps=0.1)",  0.1,   0.0, 0.1, np.pi/2),
            ("He (eps=0.3)",  0.3,   0.0, 0.3, np.pi/2),
        ]
        for name, e1, p1, e2, p2 in configs:
            G, _ = make_config(e1, p1, e2, p2)
            r = analyze(G)
            self.log(f"\n  {name}: S = {r['S']:.5f}")
            for h in r['hinges']:
                self.log(f"    {h['tri']} {h['type']}"
                         f"  det={h['det']:.6f}"
                         f"  θ={h['theta']:.4f}"
                         f"  δ={h['delta']:.4f}")
        self.check("Anatomy complete", True)


if __name__ == "__main__":
    CorrectGeometry().execute()
