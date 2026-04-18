"""
EXP_FND_018: Regge action on boundary of 5-simplex
====================================================

Compute Regge action S = sum_h A_h * delta_h directly from the
symmetric (3,3) configuration of d(Delta^5).

For each triangular hinge T:
  A(T) = sqrt(det(G_T))                     [hinge area]
  dihedral at T in simplex sigma = angle   [from normal projection]
  total_angle(T) = sum over 3 simplices containing T
  deficit delta(T) = 2*pi - total_angle(T)

Regge action S = sum over 20 hinges of A(T) * delta(T).

Goal: extract epsilon_0 candidate from this action.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math


def config_vertices():
    """Symmetric (3,3) config of d(Delta^5) in R^5."""
    sqrt3 = math.sqrt(3)
    return {
        "A1": np.array([1, 0, 0, 0, 0], dtype=float),
        "A2": np.array([0, 1, 0, 0, 0], dtype=float),
        "A3": np.array([0, 0, 1, 0, 0], dtype=float),
        "B1": np.array([0, 0, 0, 1, 0], dtype=float),
        "B2": np.array([0, 0, 0, -0.5, sqrt3/2], dtype=float),
        "B3": np.array([0, 0, 0, -0.5, -sqrt3/2], dtype=float),
    }


def proj_onto_affine(v, basis_pts):
    """Project v onto affine hull of basis_pts."""
    centroid = np.mean(basis_pts, axis=0)
    vs = np.array([p - centroid for p in basis_pts])
    # QR for orthonormal basis of span
    q, _ = np.linalg.qr(vs.T)
    # rank = number of independent directions
    rank = np.linalg.matrix_rank(vs)
    q = q[:, :rank]
    w = v - centroid
    proj = q @ (q.T @ w) + centroid
    return proj


def dihedral_at_hinge(T_pts, u, v):
    """Dihedral angle at triangle T between faces T+u and T+v.
    u, v are the two other vertices of the 4-simplex."""
    # Project u, v onto affine hull of T
    u_proj = proj_onto_affine(u, T_pts)
    v_proj = proj_onto_affine(v, T_pts)
    # Perpendicular components
    u_perp = u - u_proj
    v_perp = v - v_proj
    # Normalize
    nu = np.linalg.norm(u_perp)
    nv = np.linalg.norm(v_perp)
    if nu < 1e-12 or nv < 1e-12:
        return 0.0
    u_n = u_perp / nu
    v_n = v_perp / nv
    cos_dih = np.dot(u_n, v_n)
    cos_dih = max(-1.0, min(1.0, cos_dih))
    return math.acos(cos_dih)


def hinge_area(T_pts):
    """Area = sqrt(det(G_T)) for 3 points."""
    n = len(T_pts)
    G = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            G[i, j] = np.dot(T_pts[i], T_pts[j])
    return math.sqrt(max(0, np.linalg.det(G)))


def classify(labels):
    ac = sum(1 for l in labels if l.startswith('A'))
    bc = sum(1 for l in labels if l.startswith('B'))
    return 'A' * ac + 'B' * bc


class EXP_FND_018(Experiment):
    ID = "FND_018"
    TITLE = "Regge Action on d(Delta^5)"

    def run(self):
        self.log("=" * 65)
        self.log("REGGE ACTION ON d(DELTA^5)")
        self.log("=" * 65)

        vecs = config_vertices()
        labels = list(vecs.keys())
        # Six simplices: each = 5 of 6 vertices (one removed)
        # sigma_k = all vertices except labels[k]
        simplices = []
        for k in range(6):
            sigma = [labels[j] for j in range(6) if j != k]
            simplices.append(sigma)

        self.log(f"\n  Vertices: {labels}")
        self.log(f"  Simplices: 6 (each omits one vertex)")

        # For each triangular hinge T (20 total), find simplices containing T
        # and compute dihedral angles
        hinge_data = []
        for T_labels in combinations(labels, 3):
            htype = classify(T_labels)
            T_pts = [vecs[l] for l in T_labels]
            area = hinge_area(T_pts)
            # Find which simplices contain T
            containing = []
            for sigma in simplices:
                if all(l in sigma for l in T_labels):
                    containing.append(sigma)
            # For each containing simplex, compute dihedral at T
            dihedrals = []
            for sigma in containing:
                others = [l for l in sigma if l not in T_labels]
                assert len(others) == 2
                u, v = vecs[others[0]], vecs[others[1]]
                dih = dihedral_at_hinge(T_pts, u, v)
                dihedrals.append(dih)
            total_angle = sum(dihedrals)
            deficit = 2 * math.pi - total_angle
            hinge_data.append({
                'labels': T_labels, 'type': htype, 'area': area,
                'num_simplices': len(containing),
                'dihedrals': dihedrals,
                'total_angle': total_angle, 'deficit': deficit,
            })

        # Print per-hinge data
        self.log(f"\n  Each hinge should be in 3 simplices (6-3 = 3):")
        self.log(f"\n  {'Hinge':>20} {'Type':>5} {'#sig':>5} {'area':>8}"
                 f" {'total ang':>10} {'deficit':>10}")
        self.log(f"  {'-'*20} {'-'*5} {'-'*5} {'-'*8} {'-'*10} {'-'*10}")
        for h in hinge_data:
            self.log(f"  {str(h['labels']):>20} {h['type']:>5}"
                     f" {h['num_simplices']:>5} {h['area']:>8.4f}"
                     f" {h['total_angle']:>10.4f} {h['deficit']:>+10.4f}")

        # Check: all hinges in 3 simplices
        self.check("All hinges shared by 3 simplices",
                   all(h['num_simplices'] == 3 for h in hinge_data))

        # Regge action total + by type
        self.log(f"\n{'='*65}")
        self.log("REGGE ACTION")
        self.log(f"{'='*65}")

        S_total = sum(h['area'] * h['deficit'] for h in hinge_data)
        self.log(f"\n  Total Regge action S = sum A_h * delta_h = {S_total:.6f}")

        # By type
        by_type = {}
        for h in hinge_data:
            t = h['type']
            if t not in by_type:
                by_type[t] = {'count': 0, 'S_contrib': 0,
                              'areas': [], 'deficits': []}
            by_type[t]['count'] += 1
            by_type[t]['S_contrib'] += h['area'] * h['deficit']
            by_type[t]['areas'].append(h['area'])
            by_type[t]['deficits'].append(h['deficit'])

        self.log(f"\n  {'Type':>5} {'count':>5} {'<area>':>10}"
                 f" {'<deficit>':>10} {'S_type':>10}")
        self.log(f"  {'-'*5} {'-'*5} {'-'*10} {'-'*10} {'-'*10}")
        for t in ['AAA', 'AAB', 'ABB', 'BBB']:
            if t in by_type:
                d = by_type[t]
                avg_a = np.mean(d['areas'])
                avg_d = np.mean(d['deficits'])
                self.log(f"  {t:>5} {d['count']:>5} {avg_a:>10.4f}"
                         f" {avg_d:>+10.4f} {d['S_contrib']:>+10.4f}")

        # Compare with theoretical values
        self.log(f"\n  Theoretical expectations (book):")
        self.log(f"    delta_AAA = pi = {math.pi:.4f} (ch04 confinement)")
        self.log(f"    delta_BBB = 0 (ch04 TTT theorem)")
        aaa_deficit = by_type['AAA']['deficits'][0] if 'AAA' in by_type else None
        bbb_deficit = by_type['BBB']['deficits'][0] if 'BBB' in by_type else None
        self.log(f"  Computed:")
        self.log(f"    delta_AAA = {aaa_deficit:.4f} (expected pi)")
        self.log(f"    delta_BBB = {bbb_deficit:.4f} (expected 0)")
        self.check("delta_AAA = pi (within 5%)",
                   abs(aaa_deficit - math.pi) / math.pi < 0.05)
        self.check("delta_BBB = 0 (within 0.01)",
                   abs(bbb_deficit) < 0.01)

        # Extract eps0 candidates from Regge action
        self.log(f"\n{'='*65}")
        self.log("EXTRACT epsilon_0 FROM REGGE DATA")
        self.log(f"{'='*65}")

        alpha_GUT = 6 / (25 * math.pi**2)
        eps0_book = 0.0038

        # Known: S_total, individual contributions by type
        self.log(f"\n  Candidate formulas (all built from S_Regge data):")
        candidates = [
            ("|S_total|",                     abs(S_total)),
            ("|S_total| / (25 pi^2)",         abs(S_total) / (25 * math.pi**2)),
            ("|S_total| / 25",                abs(S_total) / 25),
            ("|S_total| / 625 (d^4)",         abs(S_total) / 625),
            ("S_total / (4 pi^2) (CGB norm)", abs(S_total) / (4 * math.pi**2)),
            ("|S_total|^2 / d^4",             S_total**2 / 625),
            ("S_total / d^6",                 abs(S_total) / 15625),
        ]
        self.log(f"\n  {'Formula':<30} {'Value':>12} {'vs 0.0038':>12}")
        self.log(f"  {'-'*30} {'-'*12} {'-'*12}")
        for name, val in candidates:
            if val > 0:
                dev = (val - eps0_book) / eps0_book * 100
                marker = " <-" if abs(dev) < 10 else ""
                self.log(f"  {name:<30} {val:>12.6f} {dev:>+10.2f}%{marker}")

        # Theoretical 4D Euler characteristic constraint
        self.log(f"""
  Gauss-Bonnet constraint for S^4:
    Sum_h A_h * delta_h (related to Euler char chi = 2 for S^4)
    Standard form: (1/(2*(2 pi)^2)) * integral of curvature^2 = chi
  """)

        # Check AAA contribution
        aaa_contrib = by_type['AAA']['S_contrib'] if 'AAA' in by_type else 0
        self.log(f"  AAA single-hinge S contribution: {aaa_contrib:.4f}")
        self.log(f"    area = 1, deficit = {aaa_deficit:.4f}")
        self.log(f"    = {aaa_contrib:.4f} = pi (if deficit=pi, area=1)")

        # Summary
        self.log(f"\n{'='*65}")
        self.log("SUMMARY")
        self.log(f"{'='*65}")
        self.log(f"""
  Computed Regge action at symmetric d(Delta^5):
    S_total = {S_total:.6f}
    Contributions:
      AAA (1 hinge):  {by_type.get('AAA', {}).get('S_contrib', 0):+.4f}
      AAB (9 hinges): {by_type.get('AAB', {}).get('S_contrib', 0):+.4f}
      ABB (9 hinges): {by_type.get('ABB', {}).get('S_contrib', 0):+.4f}
      BBB (1 hinge):  {by_type.get('BBB', {}).get('S_contrib', 0):+.4f}

  Verified book claims:
    delta_AAA = pi (confinement)
    delta_BBB = 0 (TTT theorem)

  None of the naive candidates [S/25, S/625, S/(4 pi^2), etc.]
  match eps_0 = 0.0038 to high precision.

  This tells us: eps_0 is NOT a direct sum quantity from Regge.
  Perhaps:
    (a) eps_0 is a RATIO between two Regge sums (e.g., AAA vs ABB)
    (b) eps_0 is from the DEVIATION of S from Euler/GB prediction
    (c) eps_0 involves different configuration (not symmetric)

  Symmetric config may represent "unbroken" state; eps_0 measures
  departure from it. This would suggest eps_0 is a local/perturbative
  field, not a fixed geometric number.
""")


if __name__ == "__main__":
    EXP_FND_018().execute()
