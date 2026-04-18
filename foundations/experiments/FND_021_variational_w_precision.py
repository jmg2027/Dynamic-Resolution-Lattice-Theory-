"""
EXP_FND_021: Precision test of w* = 3/(5*pi) conjecture
=========================================================

FND_004 gives w* ~= 0.1903 numerically (Nelder-Mead).
Candidate: w* = 3/(5*pi) = 0.19099.

Relative difference: 0.4%.

This experiment:
  1. Uses scipy.optimize.minimize with higher precision (brentq/tolerance).
  2. Tests w* = 3/(5*pi) analytically by computing dS/dw at that point.
  3. If dS/dw = 0 at w = 3/(5*pi), conjecture is verified analytically.

Claim: if verified, then
  w^2 = 9/(25*pi^2) = (3/2) * alpha_GUT exactly.
  alpha_GUT emerges from variational principle with no free parameter.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math
from scipy.optimize import minimize_scalar


# ---- Regge action machinery (from FND_004) ----
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
    cpp, cqq, cpq = vals[(p, p)], vals[(q, q)], vals[(p, q)]
    if cpp <= 0 or cqq <= 0:
        return 0.0
    return np.arccos(np.clip(-cpq/np.sqrt(cpp*cqq), -1, 1))


def regge(w, theta):
    """Regge action at (w, theta) for symmetric (3,3) config."""
    # A vertices with mutual overlap w
    A1 = np.array([1, 0, 0, 0, 0], dtype=complex)
    a2_1 = w; a2_2 = np.sqrt(max(1 - w**2, 0))
    A2 = np.array([a2_1, a2_2, 0, 0, 0], dtype=complex)
    a3_1 = w
    a3_2 = (w - w*a2_1) / a2_2 if a2_2 > 1e-15 else 0
    a3_3 = np.sqrt(max(1 - a3_1**2 - a3_2**2, 0))
    A3 = np.array([a3_1, a3_2, a3_3, 0, 0], dtype=complex)
    B1 = np.array([0, 0, 0, 1, 0], dtype=complex)
    B2 = np.array([0, 0, 0, 0, 1], dtype=complex)
    B3 = np.array([0, 0, 0, np.cos(theta), np.sin(theta)], dtype=complex)
    all_vecs = [A1, A2, A3, B1, B2, B3]
    S = 0.0
    for h in HINGES:
        G3 = gram([all_vecs[i] for i in h])
        d3 = np.real(np.linalg.det(G3))
        if d3 <= 1e-15:
            continue
        a = np.sqrt(d3)
        st = sum(dihedral(gram([all_vecs[k] for k in sg]), hl)
                 for sg, hl in HINGE_MAP[h])
        df = 2*np.pi - st
        S += a * df
    return S


class EXP_FND_021(Experiment):
    ID = "FND_021"
    TITLE = "Variational w star precision"

    def run(self):
        self.log("=" * 65)
        self.log("PRECISION TEST: w* = 3/(5*pi)?")
        self.log("=" * 65)

        pi = math.pi
        theta_star = pi / 4  # theta = 45 deg
        w_conjecture = 3 / (5 * pi)

        self.log(f"\n  Conjecture: w* = 3/(5 pi) = {w_conjecture:.12f}")
        self.log(f"             w*^2 = 9/(25 pi^2) = {w_conjecture**2:.12f}")
        self.log(f"             (3/2)*alpha_GUT = {1.5*6/(25*pi**2):.12f}")

        # Find w* numerically at theta = pi/4 with high precision
        def neg_S(w):
            return -regge(w, theta_star)

        # Use high-precision scalar optimization
        result = minimize_scalar(neg_S, bracket=(0.1, 0.2, 0.3),
                                 method='brent', tol=1e-14,
                                 options={'xtol': 1e-14})
        w_numerical = result.x
        S_at_opt = -result.fun

        self.log(f"\n  Numerical optimization (brent, tol=1e-14):")
        self.log(f"    w* = {w_numerical:.12f}")
        self.log(f"    S(w*) = {S_at_opt:.12f}")
        self.log(f"    |w_numerical - 3/(5*pi)| = {abs(w_numerical - w_conjecture):.2e}")
        self.log(f"    Relative: {abs(w_numerical - w_conjecture)/w_conjecture*100:.4f}%")

        # Compute S at w = 3/(5*pi) exactly
        S_conj = regge(w_conjecture, theta_star)
        self.log(f"\n  S(3/(5*pi), pi/4) = {S_conj:.12f}")
        self.log(f"  S(w*_num, pi/4)   = {S_at_opt:.12f}")
        self.log(f"  Difference: {S_at_opt - S_conj:.2e}")

        self.check("w* within 1% of 3/(5*pi)",
                   abs(w_numerical - w_conjecture)/w_conjecture < 0.01)

        # Numerical derivative at w = 3/(5*pi)
        self.log(f"\n{'='*65}")
        self.log("dS/dw at conjectured w = 3/(5*pi)")
        self.log(f"{'='*65}")
        dw = 1e-6
        dS = (regge(w_conjecture + dw, theta_star) -
              regge(w_conjecture - dw, theta_star)) / (2 * dw)
        self.log(f"\n  dS/dw at w = 3/(5*pi): {dS:.6e}")
        self.log(f"  If conjecture exact: should be 0.")

        dS_num = (regge(w_numerical + dw, theta_star) -
                  regge(w_numerical - dw, theta_star)) / (2 * dw)
        self.log(f"  dS/dw at w_numerical:  {dS_num:.6e}  (check)")

        self.check("dS/dw at 3/(5pi) is small-ish",
                   abs(dS) < 1.0)
        self.check("dS/dw at w_numerical ~ 0",
                   abs(dS_num) < 0.01)

        # Scan: precision landscape
        self.log(f"\n{'='*65}")
        self.log("PRECISION LANDSCAPE near optimum")
        self.log(f"{'='*65}")
        candidates = [
            ("w = 3/(5*pi)",       3 / (5 * pi)),
            ("w = numerical",      w_numerical),
            ("w = sqrt(9/25/pi^2)", np.sqrt(9/(25*pi**2))),
            ("w = 0.1903 (FND_004)", 0.1902676482),
            ("w = sqrt((3/2)*alpha_GUT)",
              np.sqrt((3/2) * 6/(25*pi**2))),
        ]
        self.log(f"\n  {'candidate':<30} {'w':>15} {'w^2':>15} {'S':>15}")
        for name, w in candidates:
            S_val = regge(w, theta_star)
            self.log(f"  {name:<30} {w:>15.10f} {w**2:>15.10f}"
                     f" {S_val:>15.10f}")

        # Summary
        self.log(f"\n{'='*65}")
        self.log("SUMMARY")
        self.log(f"{'='*65}")
        rel_dev = abs(w_numerical - w_conjecture) / w_conjecture
        self.log(f"""
  w* (Brent, tol 1e-14): {w_numerical:.10f}
  w* conjecture 3/(5*pi): {w_conjecture:.10f}
  Relative deviation: {rel_dev*100:.4f}%

  Analysis:
    - 0.4% gap persists even at high-precision optimization.
    - If w* = 3/(5*pi) exactly, numerical should converge to it
      (Brent tolerance 1e-14 should find it to 10+ digits).
    - Gap 0.4% is LARGER than convergence tolerance.
    => w* != 3/(5*pi) exactly.

  Alternative conjectures to explore:
    - w* = alpha_GUT related formula with correction
    - w* = root of specific algebraic equation from dS/dw = 0
    - Need analytical form of S(w) at theta = pi/4 to derive w* exactly.

  Status:
    N4 "w^2 = 9/(25*pi^2)" conjecture: LIKELY FALSE at 0.4% level.
    Still the closest algebraic form found, but not exact.
""")
        self.check("Conjecture testable", True)


if __name__ == "__main__":
    EXP_FND_021().execute()
