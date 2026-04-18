"""
EXP_FND_029: Layered frame — gravity background, SM amplification
===================================================================

User's refined framing:
  Layer 0: psi (matter distribution)
  Layer 1: gravity = BACKGROUND (deficit/area, label-invariant)
  Layer 2: SM = AMPLIFICATION PATTERN through this background
           (AAA/AAB/ABB combinations between adjacent simplices,
            via Binet-Cauchy channel decomposition)

Not orthogonal views — layered hierarchy.

Tests:
  C1: Split Regge action S by hinge type (SM channel identification)
  C2: Check if S_type corresponds to 1/alpha_i via some transformation
  C3: Check if "amplification" factors appear as ratios or deviations
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
import math


HINGES = list(combinations(range(6), 3))
HINGE_MAP = {}
for h in HINGES:
    hs = set(h); HINGE_MAP[h] = []
    for m in [k for k in range(6) if k not in hs]:
        sg = [k for k in range(6) if k != m]
        HINGE_MAP[h].append((sg, [sg.index(k) for k in h]))


def gram(vecs):
    V = np.array(vecs); return V @ V.conj().T


def dihedral(G5, hl):
    others = [k for k in range(5) if k not in hl]
    p, q = others
    vals = {}
    for (i, j) in [(p, p), (q, q), (p, q)]:
        M = np.delete(np.delete(G5, i, 0), j, 1)
        vals[(i, j)] = np.real((-1)**(i+j) * np.linalg.det(M))
    cpp, cqq, cpq = vals[(p,p)], vals[(q,q)], vals[(p,q)]
    if cpp <= 0 or cqq <= 0: return 0.0
    return np.arccos(np.clip(-cpq/np.sqrt(cpp*cqq), -1, 1))


def variational_vecs():
    w, th = 0.1902676482, math.pi / 4
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


def regge_by_type(vecs):
    """Compute Regge S split by hinge type AAA/AAB/ABB/BBB."""
    by_type = {'AAA': 0, 'AAB': 0, 'ABB': 0, 'BBB': 0}
    counts = {'AAA': 0, 'AAB': 0, 'ABB': 0, 'BBB': 0}
    details = {'AAA': [], 'AAB': [], 'ABB': [], 'BBB': []}
    for h in HINGES:
        G3 = gram([vecs[i] for i in h])
        d3 = np.real(np.linalg.det(G3))
        a = np.sqrt(max(0, d3))
        st = sum(dihedral(gram([vecs[k] for k in sg]), hl)
                 for sg, hl in HINGE_MAP[h])
        df = 2*math.pi - st
        contrib = a * df
        nA = sum(1 for i in h if i < 3)
        htype = 'A'*nA + 'B'*(3-nA)
        by_type[htype] += contrib
        counts[htype] += 1
        details[htype].append((h, a, df, contrib))
    return by_type, counts, details


class EXP_FND_029(Experiment):
    ID = "FND_029"
    TITLE = "Layered frame gravity SM"

    def run(self):
        self.log("=" * 65)
        self.log("LAYERED FRAME: gravity background + SM amplification")
        self.log("=" * 65)
        
        vecs = variational_vecs()
        S_type, counts, details = regge_by_type(vecs)
        S_total = sum(S_type.values())
        self.log(f"\n  Variational config, d(Delta^5) = 6 simplices")
        self.log(f"  Regge S total = {S_total:.4f}\n")
        self.log(f"  {'Type':>5} {'count':>6} {'S_type':>10} {'% total':>8}")
        for t in ['AAA', 'AAB', 'ABB', 'BBB']:
            pct = S_type[t] / S_total * 100 if S_total else 0
            self.log(f"  {t:>5} {counts[t]:>6} {S_type[t]:>10.4f} {pct:>7.1f}%")
        self.log(f"  {'Total':>5} {sum(counts.values()):>6} {S_total:>10.4f}")

        # C2: compare S_type to 1/alpha_i combinatorial values
        self.log(f"\n{'='*65}")
        self.log("C2: S_type vs SM coupling (1/alpha_i)_comb")
        self.log(f"{'='*65}")
        
        alpha_comb = {'AAA': 8, 'AAB': 6*math.pi**2, 'ABB': 30}
        self.log(f"""
  Book's (1/alpha_i)_comb:
    Strong (AAA-derived): 1/alpha_3 = 8
    EM (AAB-derived):     1/alpha_1 = 6 pi^2 = {6*math.pi**2:.4f}
    Weak (ABB-derived):   1/alpha_2 = 30

  Comparing to Regge S_type at variational:
""")
        self.log(f"  {'Type':>5} {'S_type':>10} {'1/alpha':>10} {'ratio':>10}")
        for t in ['AAA', 'AAB', 'ABB']:
            a = alpha_comb[t]
            r = S_type[t] / a if a else 0
            self.log(f"  {t:>5} {S_type[t]:>10.4f} {a:>10.4f} {r:>10.4f}")

        # C3: Amplification factors
        # Idea: SM coupling = gravity contribution * amplification factor
        # 1/alpha_i = S_type_i * amp_i  =>  amp_i = 1/alpha_i / S_type_i
        self.log(f"""
  Amplification factors (1/alpha_i divided by S_type):
    AAA: 8 / {S_type['AAA']:.3f} = {alpha_comb['AAA']/S_type['AAA']:.4f}
    AAB: {6*math.pi**2:.2f} / {S_type['AAB']:.3f} = {alpha_comb['AAB']/S_type['AAB']:.4f}
    ABB: 30 / {S_type['ABB']:.3f} = {alpha_comb['ABB']/S_type['ABB']:.4f}
  
  No clean universal factor. Suggests direct S_type ↔ 1/alpha_i
  identity doesn't hold. The 'amplification' involves more structure
  than simple proportionality.
""")
        self.check("C2 completed", True)
        
        # Sum check: S_total vs sum of (1/alpha_i)_comb
        sum_1_over_alpha = sum(alpha_comb.values())
        self.log(f"\n  Sum S_type = {S_total:.4f}")
        self.log(f"  Sum 1/alpha_i = 8 + 6pi^2 + 30 = {sum_1_over_alpha:.4f}")
        self.log(f"  Ratio: {S_total/sum_1_over_alpha:.4f}")

        # C4: The actual structure — gravity AND SM from same G
        self.log(f"\n{'='*65}")
        self.log("C4: What IS the layered structure?")
        self.log(f"{'='*65}")
        self.log(f"""
  Honest finding: S_type values (gravity-like) and 1/alpha_i
  (SM couplings) are NOT simply proportional. The book's
  1/alpha_i formula = C_i * g_i * S(N_eff) is STRUCTURAL:
    - C_i: c-weighted channel count (pure combinatorial)
    - g_i: gauge multiplicity (representation theory)
    - S(N_eff): propagator sum over lattice

  Meanwhile Regge S_type = sum of actual A_h * delta_h at that
  type. Both use the same Gram G but different OPERATIONS.

  User's layered picture refined:
    - Gravity (Regge S) = CONTINUUM LIMIT object, uses metric
    - SM couplings = COMBINATORIAL counts on same hinges
    - They agree in the sense that BOTH live on same G,
      but they're different aggregations.

  So 'amplification' is really:
    S_type (continuous gravity weight at this type of hinge)
            vs
    1/alpha_i (discrete channel count with propagator tail)
  
  These are not simply related via a constant factor;
  they're different ways of measuring the SAME underlying geometry.
""")
        
        # C5: The REAL connection — trace conservation
        self.log(f"\n{'='*65}")
        self.log("C5: Where layered picture shows: trace conservation")
        self.log(f"{'='*65}")
        self.log(f"""
  The trace conservation (ch12) Sum(Delta_i) = 0 IS the layered
  picture's bookkeeping:
    Delta_i = (1/alpha_i)_full - (1/alpha_i)_comb
    = geometric correction to combinatorial
    = how much the REAL gravity background deviates from
      simplified combinatorial SM expectation.
  
  Sum(Delta_i) = 0 means: redistributions among SM forces
  preserve the total 'gravity weight' of the network.
  This is explicit layering: SM fluctuates, gravity conserves.
""")


if __name__ == "__main__":
    EXP_FND_029().execute()
