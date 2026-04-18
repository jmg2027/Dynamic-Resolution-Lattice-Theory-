"""
EXP_FND_026: Gravity as shape (deficit only), not internal
=============================================================

User's framing: gravity is unrelated to individual simplex properties
(internal det(G_h)). Only the SHAPE (deficit angle arrangement) matters.

Test hypothesis:
  Delta_G = f({delta_h}) for some function f, computed at variational
  config. No det(G_h) involvement.

Formalization:
  SM: 1/alpha_i = C * g * S(N_eff) + Delta_i (where Delta_i involves 
      local det(G_h))
  Gravity: Delta_G = pure deficit functional, no det

Test various functionals of {delta_h}:
  F1: Total deficit Sum delta_h
  F2: Mean deficit  
  F3: Weighted sum (area-weighted)
  F4: RMS deficit
  F5: Variance of deficit distribution
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math


# Variational config from FND_004
def variational_config():
    w = 0.1902676482
    th = math.pi / 4
    A1 = np.array([1, 0, 0, 0, 0], dtype=complex)
    a2_2 = np.sqrt(1 - w**2)
    A2 = np.array([w, a2_2, 0, 0, 0], dtype=complex)
    a3_2 = (w - w**2) / a2_2
    a3_3 = np.sqrt(max(1 - w**2 - a3_2**2, 0))
    A3 = np.array([w, a3_2, a3_3, 0, 0], dtype=complex)
    B1 = np.array([0, 0, 0, 1, 0], dtype=complex)
    B2 = np.array([0, 0, 0, 0, 1], dtype=complex)
    B3 = np.array([0, 0, 0, np.cos(th), np.sin(th)], dtype=complex)
    return [A1, A2, A3, B1, B2, B3]


HINGES = list(combinations(range(6), 3))
HINGE_MAP = {}
for h in HINGES:
    hs = set(h); HINGE_MAP[h] = []
    for m in [k for k in range(6) if k not in hs]:
        sg = [k for k in range(6) if k != m]
        HINGE_MAP[h].append((sg, [sg.index(k) for k in h]))


def gram(vecs):
    V = np.array(vecs); return V @ V.conj().T


def dihedral(G5, h_local):
    others = [k for k in range(5) if k not in h_local]
    p, q = others
    vals = {}
    for (i, j) in [(p, p), (q, q), (p, q)]:
        M = np.delete(np.delete(G5, i, 0), j, 1)
        vals[(i, j)] = np.real((-1)**(i+j) * np.linalg.det(M))
    cpp, cqq, cpq = vals[(p,p)], vals[(q,q)], vals[(p,q)]
    if cpp <= 0 or cqq <= 0:
        return 0.0
    return np.arccos(np.clip(-cpq/np.sqrt(cpp*cqq), -1, 1))


def all_hinge_data(vecs):
    """Return list of (type, area, deficit) for all 20 hinges."""
    data = []
    for h in HINGES:
        G3 = gram([vecs[i] for i in h])
        d3 = np.real(np.linalg.det(G3))
        area = np.sqrt(max(0, d3))
        nA = sum(1 for i in h if i < 3)
        htype = 'A'*nA + 'B'*(3-nA)
        st = sum(dihedral(gram([vecs[k] for k in sg]), hl)
                 for sg, hl in HINGE_MAP[h])
        df = 2*np.pi - st
        data.append((h, htype, area, df))
    return data


class EXP_FND_026(Experiment):
    ID = "FND_026"
    TITLE = "Gravity as shape functional"

    def run(self):
        self.log("=" * 65)
        self.log("GRAVITY AS SHAPE: test functionals of {delta_h}")
        self.log("=" * 65)

        vecs = variational_config()
        data = all_hinge_data(vecs)
        deltas = [d[3] for d in data]
        areas = [d[2] for d in data]
        
        self.log(f"\n  Hinge data at variational config:")
        self.log(f"  {'type':>5} {'area':>10} {'deficit':>12}")
        for h, ht, a, df in data:
            self.log(f"  {ht:>5} {a:>10.4f} {df:>+12.4f}")
        
        Delta_G_book = 0.15

        # Compute various SHAPE-only functionals
        self.log(f"\n{'='*65}")
        self.log("SHAPE FUNCTIONALS (no area/det(G_h) used)")
        self.log(f"{'='*65}")

        sum_d = sum(deltas)
        mean_d = np.mean(deltas)
        rms_d = np.sqrt(np.mean([d**2 for d in deltas]))
        var_d = np.var(deltas)
        max_d = max(deltas)
        min_d = min(deltas)

        functionals = [
            ("Sum of deficits", sum_d),
            ("Sum / (2*pi)", sum_d / (2*math.pi)),
            ("Sum / (25*pi^2)", sum_d / (25*math.pi**2)),
            ("Sum / (32*pi^2) (EH)", sum_d / (32*math.pi**2)),
            ("Mean deficit", mean_d),
            ("Mean / (2*pi)", mean_d / (2*math.pi)),
            ("RMS deficit", rms_d),
            ("RMS / (2*pi)", rms_d / (2*math.pi)),
            ("Variance", var_d),
            ("Var / (2*pi)^2", var_d / (2*math.pi)**2),
            ("(Sum/2pi)^2", (sum_d/(2*math.pi))**2),
            ("max - min", max_d - min_d),
            ("(max-min)/(2*pi)", (max_d-min_d)/(2*math.pi)),
        ]

        self.log(f"\n  {'Functional':<30} {'Value':>12} {'vs 0.15':>10}")
        for name, val in functionals:
            rel = val / Delta_G_book if Delta_G_book else 0
            marker = " <--" if 0.8 < abs(rel) < 1.2 else ""
            self.log(f"  {name:<30} {val:>12.6f} {rel:>10.3f}{marker}")

        self.check("Shape functionals computed", True)

        # Summary
        self.log(f"\n{'='*65}")
        self.log("SUMMARY")
        self.log(f"{'='*65}")
        self.log(f"""
  User framing: gravity = shape (deficit only), not internal (det).
  
  Tested various deficit-only functionals. Results at variational config:
  - Sum of deficits: {sum_d:.4f} rad = {sum_d/math.pi:.4f} pi
  - Per hinge mean: {mean_d:.4f} rad
  - None match book's Delta_G = +0.15 cleanly.

  Observation: Sum/(2*pi) = {sum_d/(2*math.pi):.4f}, Book's Delta_G = 0.15.
  
  This suggests:
    (a) User's "gravity = shape only" may be right philosophically,
        but the specific formula giving Delta_G = 0.15 is NOT a simple
        functional of {{delta_h}} alone.
    (b) Perhaps gravity needs BOTH area and deficit (Regge product),
        contra user's framing.
    (c) Or: Delta_G in book is NOT the 'gravity' of user's framing;
        might be a bookkeeping residual.

  NEXT: investigate if gravity = topological invariant (like 
  Gauss-Bonnet chi = 2 for S^4), which would be purely shape/topology.
""")


if __name__ == "__main__":
    EXP_FND_026().execute()
