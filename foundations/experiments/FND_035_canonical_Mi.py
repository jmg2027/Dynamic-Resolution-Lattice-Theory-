"""
EXP_FND_035: Canonical M_i weights from (3,2) simplex geometry
================================================================

Phase A2 of physics-math bridge roadmap: G-M_i geometric weights.

Context:
- Book ch12: Δ_i = Sgn · (1/α_i)_comb · M_i · ε₀
  with M_Strong = 13.75, M_Weak = 3.5, M_EM = 1.0 (asserted, not derived).
- BinetCauchy: 1+12+12=25 channels split as AAA, AAB, ABB.
  AAA → Strong (1 channel)
  AAB → EM    (12 channels)
  ABB → Weak  (12 channels)
- Per-hinge counts in (3,2) simplex:
  AAA: C(3,3)·C(2,0) = 1 hinge
  AAB: C(3,2)·C(2,1) = 6 hinges
  ABB: C(3,1)·C(2,2) = 3 hinges
  Total = 10 = C(5,3) ✓
- c-weighted channels: 1, 6·2=12, 3·4=12 (c=2).

This experiment tests: are M_i derivable from hinge Gram determinants
at the variational minimum (w*, θ=π/4)?

Candidate formulas to test:
  (F1) M_i = Σ_h∈class √det(G_h) / C_i       [avg hinge area per channel]
  (F2) M_i = (hinges_i · c^k · f(w*,θ*))      [per-class weight]
  (F3) M_i = d² / (hinges_i · gauge_i)        [inverse gauge density]
  (F4) M_i from book values 13.75, 3.5, 1.0 ← target
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math


# ---- Hinge enumeration: 10 hinges of (3,2) simplex ----
# Vertex labels: A1=0, A2=1, A3=2, B1=3, B2=4
# class: 'AAA', 'AAB', 'ABB', 'BBB'
def hinge_class(h):
    nA = sum(1 for v in h if v < 3)
    nB = 3 - nA
    return {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[nA]


HINGES = list(combinations(range(5), 3))
HINGE_BY_CLASS = {'AAA': [], 'AAB': [], 'ABB': [], 'BBB': []}
for h in HINGES:
    HINGE_BY_CLASS[hinge_class(h)].append(h)


def build_vectors(w, theta):
    """Build 5 unit vectors for symmetric (3,2) config at (w, theta).
    A-A overlaps: w. B-B overlaps: cos(theta). A-B overlaps: 0 (orthogonal blocks).
    """
    A1 = np.array([1, 0, 0, 0, 0], dtype=float)
    a2_2 = np.sqrt(max(1 - w*w, 0))
    A2 = np.array([w, a2_2, 0, 0, 0], dtype=float)
    a3_2 = (w - w*w)/a2_2 if a2_2 > 1e-15 else 0
    a3_3 = np.sqrt(max(1 - w*w - a3_2*a3_2, 0))
    A3 = np.array([w, a3_2, a3_3, 0, 0], dtype=float)
    B1 = np.array([0, 0, 0, 1, 0], dtype=float)
    B2 = np.array([0, 0, 0, np.cos(theta), np.sin(theta)], dtype=float)
    return [A1, A2, A3, B1, B2]


def hinge_volume(vectors, h):
    """√det(G_h) = 3-vol of parallelepiped spanned by hinge vertices."""
    V = np.array([vectors[i] for i in h])
    G = V @ V.T
    d = np.linalg.det(G)
    return math.sqrt(max(d, 0))


class EXP_FND_035(Experiment):
    ID = "FND_035"
    TITLE = "Canonical M_i from (3,2) simplex hinges"

    def run(self):
        pi = math.pi
        w_star = 0.19026441664311
        theta_star = pi / 4
        w0 = 3 / (5 * pi)

        self.log("=" * 65)
        self.log("FND_035: Canonical M_i from hinge geometry")
        self.log("=" * 65)
        self.log(f"\n  Config: w* = {w_star:.10f}, θ* = π/4")
        self.log(f"  Book M_i: Strong=13.75, Weak=3.5, EM=1.0")
        self.log(f"  Class assign: AAA→Strong, AAB→EM, ABB→Weak")
        self.log(f"  Hinges per class: AAA=1, AAB=6, ABB=3 (total 10)")
        self.log(f"  c-weighted channels: 1, 12, 12 (total 25=d²)")

        vecs_star = build_vectors(w_star, theta_star)
        vecs_w0 = build_vectors(w0, theta_star)

        # ---- Route 1: hinge volumes per class ----
        self.log(f"\n{'='*65}\nRoute 1: √det(G_h) per hinge class\n{'='*65}")

        def class_stats(vecs, label):
            self.log(f"\n  --- {label} ---")
            results = {}
            for cls in ['AAA', 'AAB', 'ABB']:
                hinges = HINGE_BY_CLASS[cls]
                vols = [hinge_volume(vecs, h) for h in hinges]
                total = sum(vols)
                avg = total / len(hinges) if hinges else 0
                vol_str = [f'{v:.6f}' for v in vols]
                self.log(f"  {cls}: {len(hinges)} hinges, vols={vol_str}")
                self.log(f"       Σvol={total:.6f}, avg={avg:.6f}")
                results[cls] = (total, avg, vols)
            return results

        stats_star = class_stats(vecs_star, f"w=w*={w_star:.6f}")
        stats_w0 = class_stats(vecs_w0, f"w=w₀=3/(5π)={w0:.6f}")

        # ---- Route 2: ratio of Σvol per class vs book M_i ----
        self.log(f"\n{'='*65}")
        self.log("Route 2: Σvol ratios vs book M_i")
        self.log("="*65)

        for stats, label in [(stats_star, 'w*'), (stats_w0, 'w₀')]:
            AAA = stats['AAA'][0]
            AAB = stats['AAB'][0]
            ABB = stats['ABB'][0]
            self.log(f"\n  --- at {label} ---")
            self.log(f"  Σvol(AAA) = {AAA:.6f}  [M_Strong = 13.75]")
            self.log(f"  Σvol(AAB) = {AAB:.6f}  [M_EM     = 1.0]")
            self.log(f"  Σvol(ABB) = {ABB:.6f}  [M_Weak   = 3.5]")
            if AAA > 0:
                r_weak = ABB / AAA
                r_em = AAB / AAA
                self.log(f"  ratios (AAA=1): AAB={r_em:.4f}, ABB={r_weak:.4f}")
                self.log(f"  book (M_Strong=1 norm):")
                self.log(f"    M_EM/M_Strong   = {1/13.75:.4f}")
                self.log(f"    M_Weak/M_Strong = {3.5/13.75:.4f}")

        AAA = stats_star['AAA'][0]
        AAB = stats_star['AAB'][0]
        ABB = stats_star['ABB'][0]
        book_em = 1.0 / 13.75
        book_weak = 3.5 / 13.75
        self.check("AAB/AAA ≈ M_EM/M_Strong within 30%",
                   abs((AAB/AAA) - book_em) / book_em < 0.30)
        self.check("ABB/AAA ≈ M_Weak/M_Strong within 30%",
                   abs((ABB/AAA) - book_weak) / book_weak < 0.30)

        # ---- Route 3: c-weighted ratios (multiply by c^k) ----
        self.log(f"\n{'='*65}")
        self.log("Route 3: c-weighted Σvol (c^0, c^1, c^2 = 1, 2, 4)")
        self.log("="*65)
        c = 2
        cw_AAA = 1 * AAA
        cw_AAB = c * AAB
        cw_ABB = c*c * ABB
        self.log(f"\n  c-weighted at w*:")
        self.log(f"    1·Σvol(AAA) = {cw_AAA:.6f}")
        self.log(f"    2·Σvol(AAB) = {cw_AAB:.6f}")
        self.log(f"    4·Σvol(ABB) = {cw_ABB:.6f}")
        if cw_AAA > 0:
            self.log(f"  ratios (AAA=1): AAB={cw_AAB/cw_AAA:.4f},"
                     f" ABB={cw_ABB/cw_AAA:.4f}")

        # ---- Route 4: other candidate formulas ----
        self.log(f"\n{'='*65}")
        self.log("Route 4: alternative M_i formulas")
        self.log("="*65)

        # Candidate formulas: combinations of (n_A, n_B, channel count, hinges)
        n_A, n_B, d = 3, 2, 5
        cands = [
            ("Σvol / C (channel norm)",
             AAA/1, AAB/12, ABB/12),
            ("Σvol / hinges (per-hinge)",
             AAA/1, AAB/6, ABB/3),
            ("d² / (hinges·gauge)",
             d*d/(1*8), d*d/(6*3), d*d/(3*2)),
            ("book values",
             13.75, 1.0, 3.5),
        ]
        self.log(f"\n  {'formula':<30} {'Strong':>10} {'EM':>10} {'Weak':>10}")
        for name, s, e, w in cands:
            self.log(f"  {name:<30} {s:>10.4f} {e:>10.4f} {w:>10.4f}")

        # ---- Summary ----
        self.log(f"\n{'='*65}\nSUMMARY\n{'='*65}")
        self.log(f"""
  Direct geometric interpretation of M_i tested.

  Σvol per class (at variational w*, θ=π/4):
    AAA = {AAA:.6f}  (1 hinge, M_Strong=13.75)
    AAB = {AAB:.6f}  (6 hinges, M_EM=1.0)
    ABB = {ABB:.6f}  (3 hinges, M_Weak=3.5)

  Direct ratio test:
    AAB/AAA (geom) = {AAB/AAA:.4f}  vs  M_EM/M_Strong = {1/13.75:.4f}
    ABB/AAA (geom) = {ABB/AAA:.4f}  vs  M_Weak/M_Strong = {3.5/13.75:.4f}

  Status:
    - If ratios match → M_i = Σ√det(G_h) per class (simple geometric).
    - If not → M_i has additional structure (e.g., S(N) series,
      c-weighting, hinge deficits rather than volumes).

  Next step:
    - If refuted, explore hinge angular DEFICIT (2π − Σθ) instead
      of volume, since Regge action uses `a·deficit`.
    - Test at varying (w, θ), check invariants.
""")


if __name__ == "__main__":
    EXP_FND_035().execute()
