"""
ATM_025: Minimal Manifold — Two Simplices Sharing a Face
Joint research by Mingu Jeong and Claude (Anthropic)

The correct geometric object for an atom is NOT a single Δ⁴,
but a simplicial MANIFOLD. ATM_024 showed θ(AAA) ≈ π/2 on
a single simplex. Two simplices sharing AAAB₁ face gives:

  δ(AAA) = 2π - π/2 - π/2 = π  ← matches book!

Manifold structure:
  Simplex 1: (A₁, A₂, A₃, B₁, B₂)  vertices (0,1,2,3,4)
  Simplex 2: (A₁, A₂, A₃, B₁, B₃)  vertices (0,1,2,3,5)
  Shared face: (A₁, A₂, A₃, B₁) — tetrahedron

  Shared hinges: 4 triangles in the face
  Boundary hinges: 6 + 6 = 12 (one simplex each)
  Total: 16 unique hinges
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from scipy.optimize import minimize
from itertools import combinations
from experiment import Experiment

ALPHA = 1 / 137.035999084
D = 5; N_S = 3; N_T = 2; Ry = 13.606

A = np.array([[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]],
             dtype=complex)

S1 = (0,1,2,3,4)  # simplex 1
S2 = (0,1,2,3,5)  # simplex 2
SHARED_FACE = (0,1,2,3)
SIMPLICES = [S1, S2]


# ── Geometry engine for manifold ──

def build_G(psi6):
    """6×6 global Gram matrix from 6 vectors in C^5."""
    return psi6 @ psi6.conj().T


def hinge_det(G, tri):
    idx = list(tri)
    return float(np.linalg.det(G[np.ix_(idx, idx)]).real)


def dihedral_in_simplex(G_global, simplex_verts, hinge):
    """Dihedral angle at a triangular hinge within one 4-simplex."""
    sv = list(simplex_verts)
    opp = [v for v in sv if v not in hinge]
    G_local = G_global[np.ix_(sv, sv)]
    det_local = np.linalg.det(G_local).real
    if abs(det_local) < 1e-15:
        return np.pi
    G_inv = np.linalg.inv(G_local)
    l, m = sv.index(opp[0]), sv.index(opp[1])
    num = -G_inv[l, m].real
    den = np.sqrt(max(1e-30, abs(G_inv[l,l].real * G_inv[m,m].real)))
    return float(np.arccos(np.clip(num / den, -1, 1)))


def get_all_hinges():
    """All unique triangles across the manifold."""
    all_tris = set()
    for sx in SIMPLICES:
        for tri in combinations(sx, 3):
            all_tris.add(tri)
    return sorted(all_tris)

ALL_HINGES = get_all_hinges()  # 16 unique hinges


def classify(tri):
    nA = sum(1 for v in tri if v < 3)
    nB_shared = sum(1 for v in tri if v == 3)  # B₁ = shared
    return {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[nA]


def deficit_angle_manifold(G, hinge):
    """δ_h on manifold = 2π - Σ(dihedral from each simplex)."""
    theta_sum = 0.0
    for sx in SIMPLICES:
        if set(hinge).issubset(set(sx)):
            theta_sum += dihedral_in_simplex(G, sx, hinge)
    return 2 * np.pi - theta_sum


def regge_action_manifold(G):
    """S = Σ_h A_h × δ_h over all 16 hinges."""
    S = 0.0
    for tri in ALL_HINGES:
        d = hinge_det(G, tri)
        if d > 0:
            S += np.sqrt(d) * deficit_angle_manifold(G, tri)
    return S


# ── Configuration builder ──

def make_psi6(eps1, phi1, eps2, phi2, eps3, phi3):
    """6 vectors: 3 A (fixed) + B₁,B₂,B₃ (variable)."""
    psi = np.zeros((6, 5), dtype=complex)
    psi[:3] = A
    for i, (e, ph) in enumerate([(eps1,phi1),(eps2,phi2),(eps3,phi3)]):
        t = np.sqrt(max(0, 1 - 3*e**2))
        psi[3+i] = [t*np.cos(ph), t*np.sin(ph), e, e, e]
    return psi


class MinimalManifold(Experiment):
    ID = "ATM_025"
    TITLE = "Minimal Manifold"

    def run(self):
        self.test1_verify_delta()
        self.test2_landscape()
        self.test3_optimize_H()
        self.test4_all_hinges()

    def test1_verify_delta(self):
        """Verify δ(AAA) = π on the 2-simplex manifold."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: delta(AAA) on manifold")
        self.log(f"  {'='*60}")
        self.log(f"  Prediction: delta = 2pi - pi/2 - pi/2 = pi")
        self.log(f"")
        self.log(f"  {'eps':>8} {'theta1':>8} {'theta2':>8}"
                 f" {'delta':>8} {'delta/pi':>8}")
        ok = True
        for eps in [0.001, 0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5]:
            psi = make_psi6(eps, 0.0, 0.0, np.pi/2, 0.0, np.pi/4)
            G = build_G(psi)
            aaa = (0, 1, 2)
            th1 = dihedral_in_simplex(G, S1, aaa)
            th2 = dihedral_in_simplex(G, S2, aaa)
            delta = 2*np.pi - th1 - th2
            self.log(f"  {eps:8.3f} {th1:8.4f} {th2:8.4f}"
                     f" {delta:8.4f} {delta/np.pi:8.4f}")
            if abs(delta/np.pi - 1.0) > 0.05:
                ok = False
        self.check("delta(AAA) = pi on manifold", ok)

    def test2_landscape(self):
        """S_manifold(eps) landscape for hydrogen."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: S_manifold(eps) for H")
        self.log(f"  B1=electron, B2,B3=temporal")
        self.log(f"  {'='*60}")
        self.log(f"  {'eps':>8} {'S_manifold':>12}")
        best_S, best_eps = -1e10, 0
        for eps in np.concatenate([
                np.linspace(0.001, 0.01, 10),
                np.linspace(0.01, 0.1, 20),
                np.linspace(0.1, 0.55, 20)]):
            psi = make_psi6(eps, 0, 0, np.pi/2, 0, np.pi/4)
            G = build_G(psi)
            Sm = regge_action_manifold(G)
            if Sm > best_S:
                best_S, best_eps = Sm, eps
            self.log(f"  {eps:8.5f} {Sm:12.5f}")
        self.log(f"\n  Maximum: eps={best_eps:.5f}, S={best_S:.5f}")
        self.check("Landscape scanned", True)

    def test3_optimize_H(self):
        """Optimize S_manifold for hydrogen."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Optimize H on manifold")
        self.log(f"  {'='*60}")
        emax = 1/np.sqrt(3) - 0.001
        results = []
        for eps0 in np.linspace(0.001, emax, 30):
            for sign in [-1, 1]:
                def obj(p, s=sign):
                    e1 = min(max(abs(p[0]), 1e-4), emax)
                    psi = make_psi6(e1, p[1], 0, np.pi/2,
                                    0, np.pi/4)
                    G = build_G(psi)
                    return s * regge_action_manifold(G)
                try:
                    res = minimize(obj, [eps0, 0],
                                   method='L-BFGS-B',
                                   bounds=[(1e-4,emax),(0,2*np.pi)],
                                   options={'maxiter':3000})
                    e1 = min(max(abs(res.x[0]), 1e-4), emax)
                    psi = make_psi6(e1, res.x[1], 0, np.pi/2,
                                    0, np.pi/4)
                    G = build_G(psi)
                    S = regge_action_manifold(G)
                    results.append((S, e1, sign))
                except Exception:
                    pass
        results.sort(key=lambda x: x[0], reverse=True)
        unique = [results[0]]
        for r in results[1:]:
            if all(abs(r[0]-u[0]) > 1e-4 for u in unique):
                unique.append(r)
        self.log(f"\n  Critical points:")
        for i, (S, eps, sgn) in enumerate(unique[:8]):
            opt = "MAX" if sgn == -1 else "min"
            self.log(f"  #{i+1}: S={S:.6f}  eps={eps:.6f}  ({opt})")
            if i == 0:
                self.log(f"       eps/alpha = {eps/ALPHA:.2f}")
                self.log(f"       eps*sqrt(3) = {eps*np.sqrt(3):.6f}")
        self.check("H optimized on manifold", len(unique) > 0)

    def test4_all_hinges(self):
        """Detailed hinge analysis at the critical point."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: Hinge anatomy at critical point")
        self.log(f"  {'='*60}")
        for eps in [0.004, 0.06]:
            psi = make_psi6(eps, 0, 0, np.pi/2, 0, np.pi/4)
            G = build_G(psi)
            S = regge_action_manifold(G)
            self.log(f"\n  eps={eps}, S_manifold={S:.5f}")
            self.log(f"  {'hinge':>12} {'type':>4} {'det':>8}"
                     f" {'n_sx':>4} {'delta':>8} {'d/pi':>6}")
            for tri in ALL_HINGES:
                d = hinge_det(G, tri)
                delta = deficit_angle_manifold(G, tri)
                typ = classify(tri)
                n_sx = sum(1 for sx in SIMPLICES
                           if set(tri).issubset(set(sx)))
                mk = "*" if n_sx == 2 else " "
                self.log(f"  {str(tri):>12} {typ:>4} {d:8.5f}"
                         f" {n_sx:3d}{mk} {delta:8.4f}"
                         f" {delta/np.pi:6.3f}")
        self.check("Anatomy complete", True)


if __name__ == "__main__":
    MinimalManifold().execute()
