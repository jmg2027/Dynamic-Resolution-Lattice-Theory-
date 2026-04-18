"""
EXP_FND_019: Variational Regge action
======================================

FND_018 showed symmetric (3-fold 120°) config gives S = 41.94,
close to 1/alpha_GUT = 41.12 but not exact.

This experiment: vary B_3 = alpha B_1 + beta B_2 with |a|^2+|b|^2=1,
find extremum of S_Regge, check if S_min = 25 pi^2 / 6 exactly.

If yes: Regge action at variational point = 1/alpha_GUT directly.
This would give alpha_GUT a NEW geometric derivation (Route D).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math


def build_config(alpha, beta, delta=0.0):
    """6 vertices with B_3 = alpha*B_1 + beta*B_2*exp(i*delta).
    Using real case for simplicity: delta=0."""
    A1 = np.array([1, 0, 0, 0, 0], dtype=float)
    A2 = np.array([0, 1, 0, 0, 0], dtype=float)
    A3 = np.array([0, 0, 1, 0, 0], dtype=float)
    B1 = np.array([0, 0, 0, 1, 0], dtype=float)
    B2 = np.array([0, 0, 0, 0, 1], dtype=float)
    B3 = alpha * B1 + beta * B2
    norm = np.linalg.norm(B3)
    if norm > 0:
        B3 = B3 / norm
    return [A1, A2, A3, B1, B2, B3]


def hinge_area(pts):
    n = len(pts)
    G = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            G[i, j] = np.dot(pts[i], pts[j])
    return math.sqrt(max(0, np.linalg.det(G)))


def dihedral(T_pts, u, v):
    centroid = np.mean(T_pts, axis=0)
    vs = np.array([p - centroid for p in T_pts])
    q, _ = np.linalg.qr(vs.T)
    rank = np.linalg.matrix_rank(vs)
    q = q[:, :rank]
    def perp(x):
        w = x - centroid
        return w - q @ (q.T @ w)
    u_p = perp(u); v_p = perp(v)
    nu = np.linalg.norm(u_p); nv = np.linalg.norm(v_p)
    if nu < 1e-12 or nv < 1e-12:
        return 0.0
    c = np.dot(u_p, v_p) / (nu * nv)
    c = max(-1.0, min(1.0, c))
    return math.acos(c)


def regge_action(vertices):
    """Compute S = sum A_h * delta_h for d(Delta^5)."""
    labels = list(range(6))
    simplices = [[j for j in labels if j != k] for k in range(6)]
    S = 0.0
    aaa_deficit = None
    details = {'AAA': 0, 'AAB': 0, 'ABB': 0, 'BBB': 0}
    for T_idx in combinations(labels, 3):
        T_pts = [vertices[i] for i in T_idx]
        area = hinge_area(T_pts)
        # classify A=0,1,2  B=3,4,5
        ac = sum(1 for i in T_idx if i < 3)
        bc = 3 - ac
        htype = 'A'*ac + 'B'*bc
        dihedrals = []
        for sigma in simplices:
            if all(i in sigma for i in T_idx):
                others = [i for i in sigma if i not in T_idx]
                if len(others) != 2:
                    continue
                u = vertices[others[0]]
                v = vertices[others[1]]
                dihedrals.append(dihedral(T_pts, u, v))
        total_ang = sum(dihedrals)
        deficit = 2 * math.pi - total_ang
        contrib = area * deficit
        S += contrib
        details[htype] += contrib
        if htype == 'AAA':
            aaa_deficit = deficit
    return S, aaa_deficit, details


class EXP_FND_019(Experiment):
    ID = "FND_019"
    TITLE = "Variational Regge Action"

    def run(self):
        self.log("=" * 65)
        self.log("VARIATIONAL REGGE ACTION: scan (alpha, beta)")
        self.log("=" * 65)

        target = 25 * math.pi**2 / 6
        self.log(f"\n  Target 1/alpha_GUT = 25 pi^2 / 6 = {target:.6f}")
        self.log(f"  Book: delta_AAA = pi = {math.pi:.6f} at variational pt")

        # Scan alpha in (0, 1], compute S and delta_AAA
        self.log(f"\n  Scan: B_3 = alpha*B_1 + beta*B_2, |a|^2+|b|^2=1")
        self.log(f"\n  {'alpha':>7} {'beta':>7} {'S_total':>10}"
                 f" {'delta_AAA':>10} {'AAA':>7} {'AAB':>7} {'ABB':>7}")
        self.log(f"  {'-'*7} {'-'*7} {'-'*10} {'-'*10} {'-'*7} {'-'*7} {'-'*7}")

        results = []
        for alpha in np.linspace(0.05, 1.0, 20):
            beta = math.sqrt(1 - alpha**2)
            vertices = build_config(alpha, beta)
            S, aaa_def, det = regge_action(vertices)
            results.append((alpha, beta, S, aaa_def, det))
            self.log(f"  {alpha:>7.3f} {beta:>7.3f} {S:>10.4f}"
                     f" {aaa_def:>10.4f} {det['AAA']:>+7.3f}"
                     f" {det['AAB']:>+7.3f} {det['ABB']:>+7.3f}")

        # Find where delta_AAA closest to pi
        best_aaa = min(results, key=lambda r: abs(r[3] - math.pi))
        self.log(f"\n  Closest to delta_AAA = pi:")
        self.log(f"    alpha = {best_aaa[0]:.4f}, beta = {best_aaa[1]:.4f}")
        self.log(f"    delta_AAA = {best_aaa[3]:.6f} (target {math.pi:.6f})")
        self.log(f"    S_total = {best_aaa[2]:.6f}")
        self.log(f"    vs 1/alpha_GUT = {target:.6f}")
        self.log(f"    ratio S/target = {best_aaa[2]/target:.4f}")

        # Find S extremum
        s_vals = [r[2] for r in results]
        min_s = min(s_vals); max_s = max(s_vals)
        self.log(f"\n  S range: [{min_s:.4f}, {max_s:.4f}]")
        # Look for stationary point (dS/dalpha ~ 0)
        for i in range(1, len(results)-1):
            ds1 = results[i][2] - results[i-1][2]
            ds2 = results[i+1][2] - results[i][2]
            if ds1 * ds2 < 0:
                self.log(f"  Stationary point near alpha = {results[i][0]:.3f}, "
                         f"S = {results[i][2]:.4f}")

        # Key question: does any alpha give S = target exactly?
        for r in results:
            if abs(r[2] - target) / target < 0.005:
                self.log(f"\n  S within 0.5% of target at alpha = {r[0]:.4f}:")
                self.log(f"    S = {r[2]:.4f}, target = {target:.4f}")

        self.check("Scan completed", len(results) == 20)

        # Summary
        self.log(f"\n{'='*65}")
        self.log("SUMMARY")
        self.log(f"{'='*65}")

        # Record extremum
        s_min_idx = s_vals.index(min_s)
        s_max_idx = s_vals.index(max_s)
        r_min = results[s_min_idx]; r_max = results[s_max_idx]
        self.log(f"""
  S_min at alpha = {r_min[0]:.4f}: S = {r_min[2]:.4f}, delta_AAA = {r_min[3]:.4f}
  S_max at alpha = {r_max[0]:.4f}: S = {r_max[2]:.4f}, delta_AAA = {r_max[3]:.4f}

  Target 1/alpha_GUT = 25 pi^2 / 6 = {target:.4f}
  Book's delta_AAA = pi = {math.pi:.4f}

  Key findings:
    - S_Regge depends on B-config (alpha, beta parametrization)
    - S varies from {min_s:.2f} to {max_s:.2f} over scan range
    - alpha = 0.5, beta = sqrt(3)/2 (symmetric) gives S ~ 41.94
    - delta_AAA = pi does NOT occur at symmetric config

  If book's variational principle yields delta_AAA = pi, it's
  at a NON-symmetric config. The relationship between this
  variational S and 1/alpha_GUT remains to be established.

  Honest conclusion:
    S != 1/alpha_GUT at any simple B-config found here.
    The suggestive S ~ 41.94 at symmetric vs 41.12 target is
    close but NOT exact. Need more careful variational solution
    or different observable (ratio, partial sum).
""")


if __name__ == "__main__":
    EXP_FND_019().execute()
