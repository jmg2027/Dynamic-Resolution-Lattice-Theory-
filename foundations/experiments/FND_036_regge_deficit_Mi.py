"""
EXP_FND_036: M_i from Regge deficit per hinge class
====================================================

Phase A2' continuation: FND_035 refuted Σ√det approach; now try
Regge deficit `(2π − Σθ_dihedral)` per class.

Context:
- Regge action: S = Σ_h a_h · δ_h  where a_h = √det(G_h), δ_h = 2π − Σθ
- FND_035: a_h alone (per class) gives wrong M_i ratios.
- This experiment: test if δ_h or a_h·δ_h per class matches M_i = {13.75, 1.0, 3.5}.

Strategy:
- (3,2) = 5 vertices, ONE 4-simplex. Around each hinge (triangle),
  single dihedral angle between the two tetrahedral 3-faces that share
  the hinge. Defect δ = 2π − θ_dihedral.
- Compute δ_h for all 10 hinges at (w*, θ=π/4).
- Aggregate per class (AAA, AAB, ABB), compare to book M_i.

Candidate routes:
  (R1) M_i = Σ_class δ_h              (pure deficit)
  (R2) M_i = Σ_class a_h·δ_h           (Regge contribution)
  (R3) M_i = Σ_class δ_h / hinges      (per-hinge deficit)
  (R4) c^k weighted variants
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math


HINGES = list(combinations(range(5), 3))


def hinge_class(h):
    nA = sum(1 for v in h if v < 3)
    return {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[nA]


HINGE_BY_CLASS = {'AAA': [], 'AAB': [], 'ABB': [], 'BBB': []}
for h in HINGES:
    HINGE_BY_CLASS[hinge_class(h)].append(h)


def build_vectors(w, theta):
    A1 = np.array([1, 0, 0, 0, 0], dtype=float)
    a2_2 = np.sqrt(max(1 - w*w, 0))
    A2 = np.array([w, a2_2, 0, 0, 0], dtype=float)
    a3_2 = (w - w*w)/a2_2 if a2_2 > 1e-15 else 0
    a3_3 = np.sqrt(max(1 - w*w - a3_2*a3_2, 0))
    A3 = np.array([w, a3_2, a3_3, 0, 0], dtype=float)
    B1 = np.array([0, 0, 0, 1, 0], dtype=float)
    B2 = np.array([0, 0, 0, np.cos(theta), np.sin(theta)], dtype=float)
    return [A1, A2, A3, B1, B2]


def gram(vectors):
    V = np.array(vectors)
    return V @ V.T


def hinge_volume(vecs, h):
    V = np.array([vecs[i] for i in h])
    G = V @ V.T
    d = np.linalg.det(G)
    return math.sqrt(max(d, 0))


def hinge_dihedral(vecs, h):
    """Dihedral angle at hinge h in the unique 4-simplex of 5 vertices.
    Uses cofactor formula:
      cos(θ) = -C_ij / √(C_ii · C_jj)
    where C is cofactor of full 5×5 Gram, {i,j} = vertices NOT in h.
    """
    G5 = gram(vecs)
    others = [k for k in range(5) if k not in h]
    i, j = others
    vals = {}
    for (a, b) in [(i, i), (j, j), (i, j)]:
        M = np.delete(np.delete(G5, a, 0), b, 1)
        vals[(a, b)] = ((-1) ** (a + b)) * np.linalg.det(M)
    cii, cjj, cij = vals[(i, i)], vals[(j, j)], vals[(i, j)]
    if cii <= 0 or cjj <= 0:
        return 0.0
    return np.arccos(np.clip(-cij / np.sqrt(cii * cjj), -1, 1))


def hinge_deficit(vecs, h):
    """δ_h = 2π − Σ dihedrals around hinge.
    In a single 4-simplex with one dihedral per hinge, δ = 2π − θ_one."""
    return 2 * math.pi - hinge_dihedral(vecs, h)


class EXP_FND_036(Experiment):
    ID = "FND_036"
    TITLE = "M_i from Regge deficit per hinge class"

    def run(self):
        pi = math.pi
        w_star = 0.19026441664311
        theta_star = pi / 4

        self.log("=" * 65)
        self.log("FND_036: M_i from Regge deficit (per class)")
        self.log("=" * 65)
        self.log(f"\n  Config: w*={w_star:.10f}, θ=π/4")
        self.log(f"  Book M_i: Strong=13.75, EM=1.0, Weak=3.5")

        vecs = build_vectors(w_star, theta_star)

        # Compute per-hinge a, δ, a·δ
        self.log(f"\n{'='*65}\nPer-hinge quantities\n{'='*65}")
        self.log(f"\n  {'hinge':<15} {'class':<5} {'a=√det':>10} "
                 f"{'θ':>10} {'δ=2π−θ':>10} {'a·δ':>10}")
        per_class = {'AAA': [], 'AAB': [], 'ABB': []}
        for h in HINGES:
            cls = hinge_class(h)
            a = hinge_volume(vecs, h)
            th = hinge_dihedral(vecs, h)
            delta = 2*pi - th
            ad = a * delta
            per_class[cls].append((a, th, delta, ad))
            self.log(f"  {str(h):<15} {cls:<5} {a:>10.6f} "
                     f"{th:>10.6f} {delta:>10.6f} {ad:>10.6f}")

        # Aggregate per class
        self.log(f"\n{'='*65}\nPer-class aggregates\n{'='*65}")
        self.log(f"\n  {'class':<5} {'N':>3} {'Σa':>10} {'Σδ':>10} "
                 f"{'Σaδ':>10} {'Σδ/N':>10} {'Σaδ/N':>10}")
        aggr = {}
        for cls in ['AAA', 'AAB', 'ABB']:
            items = per_class[cls]
            N = len(items)
            sum_a = sum(x[0] for x in items)
            sum_d = sum(x[2] for x in items)
            sum_ad = sum(x[3] for x in items)
            avg_d = sum_d / N
            avg_ad = sum_ad / N
            aggr[cls] = (N, sum_a, sum_d, sum_ad, avg_d, avg_ad)
            self.log(f"  {cls:<5} {N:>3} {sum_a:>10.4f} {sum_d:>10.4f} "
                     f"{sum_ad:>10.4f} {avg_d:>10.4f} {avg_ad:>10.4f}")

        # Test routes
        self.log(f"\n{'='*65}\nRoute tests vs book M_i\n{'='*65}")
        book = {'Strong': 13.75, 'EM': 1.0, 'Weak': 3.5}
        cls_to_force = {'AAA': 'Strong', 'AAB': 'EM', 'ABB': 'Weak'}

        def compare(name, vals_by_cls):
            """Normalize so Strong=book_strong, check EM and Weak."""
            ref_cls = 'AAA'
            ref_val = vals_by_cls[ref_cls]
            norm = book['Strong'] / ref_val if ref_val != 0 else 0
            pred = {cls: vals_by_cls[cls] * norm for cls in vals_by_cls}
            self.log(f"\n  --- {name} (normalized AAA→Strong=13.75) ---")
            for cls, f in cls_to_force.items():
                b = book[f]
                p = pred[cls]
                d = (p - b)/b*100 if b else 0
                self.log(f"    {cls}({f:<6}): pred={p:>8.4f}  book={b:>6.2f}"
                         f"  dev={d:+6.1f}%")
            return pred

        # Candidate routes
        r_Sa = {c: aggr[c][1] for c in aggr}
        r_Sd = {c: aggr[c][2] for c in aggr}
        r_Sad = {c: aggr[c][3] for c in aggr}
        r_avgd = {c: aggr[c][4] for c in aggr}
        r_avgad = {c: aggr[c][5] for c in aggr}

        compare("Σa per class (FND_035 baseline)", r_Sa)
        compare("Σδ per class (deficit sum)", r_Sd)
        compare("Σ(a·δ) per class (Regge contrib)", r_Sad)
        compare("avg δ per class (per-hinge deficit)", r_avgd)
        compare("avg (a·δ) per class (per-hinge Regge)", r_avgad)

        # c-weighted routes
        c_weights = {'AAA': 1, 'AAB': 2, 'ABB': 4}
        r_Sd_c = {c: r_Sd[c] * c_weights[c] for c in r_Sd}
        r_Sad_c = {c: r_Sad[c] * c_weights[c] for c in r_Sad}
        compare("c^k·Σδ per class", r_Sd_c)
        compare("c^k·Σaδ per class", r_Sad_c)

        # Reverse ratios (1/Σ)
        r_inv_Sa = {c: (1/r_Sa[c] if r_Sa[c] else 0) for c in r_Sa}
        r_inv_Sd = {c: (1/r_Sd[c] if r_Sd[c] else 0) for c in r_Sd}
        compare("1/Σa per class (inverse volume)", r_inv_Sa)
        compare("1/Σδ per class (inverse deficit)", r_inv_Sd)

        # Summary + checks
        self.log(f"\n{'='*65}\nSUMMARY\n{'='*65}")
        # Check each route: best = smallest total deviation across 3 forces
        routes = {
            "Σa": r_Sa, "Σδ": r_Sd, "Σaδ": r_Sad,
            "avgδ": r_avgd, "avgaδ": r_avgad,
            "c^k·Σδ": r_Sd_c, "c^k·Σaδ": r_Sad_c,
            "1/Σa": r_inv_Sa, "1/Σδ": r_inv_Sd,
        }

        def tot_dev(vals):
            ref = vals['AAA']
            norm = book['Strong'] / ref if ref else 0
            return sum(abs(vals[c]*norm - book[cls_to_force[c]]) /
                       book[cls_to_force[c]] for c in vals)

        self.log(f"\n  {'route':<15} {'total % dev':>12}")
        best_name, best_dev = None, float('inf')
        for name, vals in routes.items():
            d = tot_dev(vals) * 100
            if d < best_dev:
                best_dev, best_name = d, name
            self.log(f"  {name:<15} {d:>12.2f}")
        self.log(f"\n  Best route: {best_name} (tot dev {best_dev:.2f}%)")
        self.check("Any route total dev < 30%", best_dev < 30)
        self.check("Best route dev < 5%", best_dev < 5)


if __name__ == "__main__":
    EXP_FND_036().execute()
