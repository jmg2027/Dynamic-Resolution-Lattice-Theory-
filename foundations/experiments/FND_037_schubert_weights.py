"""
EXP_FND_037: W3 Binet–Cauchy equivariant weights on Gr(3,5)
================================================================

Math-track attempt #1: use equivariant structure of Λ³(V_A ⊕ V_B)
to derive M_i = {13.75, 1.0, 3.5}.

Session B count layer:
- C(5,3) = 10 Plücker coordinates ↔ 10 hinges
- Split: 1 AAA (Strong) + 6 AAB (EM) + 3 ABB (Weak)
- c-weighted: 1 + 12 + 12 = 25 (Binet–Cauchy completeness)

This experiment: compute T-weight (SU(3)×SU(2) Cartan charge) per
Plücker coord, aggregate per class, see what natural quantities
match M_i = {13.75, 1.0, 3.5}.

Conventions:
- SU(3) fundamental V_A with weights ω_k = (3 e_k − 1)/3 for k∈{1,2,3}
  so Σω = 0. Simple choice: ω = diag(+2,-1,-1)/3, (-1,+2,-1)/3, (-1,-1,+2)/3
  Integer-scaled: ω = (+2,-1,-1), (-1,+2,-1), (-1,-1,+2).
- SU(2) fundamental V_B weights μ = +1, -1.
- 10 Plücker coords = 3-subsets I of {A1..A3,B1..B2}.
  weight(I) = sum of weights of elements in I.

Candidate M_i formulas:
  (Q1) Σ |weight_A|²
  (Q2) Σ |weight_A|² · c^k  (c-weighted)
  (Q3) Σ (1 + |weight_B|²)
  (Q4) product formulas involving (|wA|² + |wB|²)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
from itertools import combinations
import math


# Integer-scaled SU(3) weights (×3)
OMEGA = {0: (2, -1, -1), 1: (-1, 2, -1), 2: (-1, -1, 2)}
# SU(2) weights
MU = {3: 1, 4: -1}


def coord_weight(I):
    """(w3_vec, w2_scalar) = SU(3)×SU(2) weight of Plücker coord for 3-subset I."""
    w3 = [0, 0, 0]
    w2 = 0
    for v in I:
        if v < 3:
            w = OMEGA[v]
            w3 = [w3[i] + w[i] for i in range(3)]
        else:
            w2 += MU[v]
    return tuple(w3), w2


def hinge_class(I):
    nA = sum(1 for v in I if v < 3)
    return {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[nA]


def abs_sq_weight(w3, w2):
    """|w|² in natural lattice norm (w3 is ×3-scaled so divide)."""
    return sum(x*x for x in w3)/9.0 + w2*w2


class EXP_FND_037(Experiment):
    ID = "FND_037"
    TITLE = "W3 Schubert T-weights per class"

    def run(self):
        self.log("=" * 65)
        self.log("FND_037: Schubert/Plücker T-weights per hinge class")
        self.log("=" * 65)
        self.log(f"\n  Book M_i: Strong(AAA)=13.75, EM(AAB)=1.0, Weak(ABB)=3.5")

        # Enumerate 10 Plücker coords
        subsets = list(combinations(range(5), 3))
        by_class = {'AAA': [], 'AAB': [], 'ABB': [], 'BBB': []}
        self.log(f"\n{'='*65}\nPer-coord weight table\n{'='*65}")
        self.log(f"\n  {'subset':<15} {'class':<5} {'wA=(x,y,z)/3':<20}"
                 f" {'wB':>4} {'|w|²':>8}")
        for I in subsets:
            cls = hinge_class(I)
            wA, wB = coord_weight(I)
            nsq = abs_sq_weight(wA, wB)
            by_class[cls].append((I, wA, wB, nsq))
            self.log(f"  {str(I):<15} {cls:<5} "
                     f"{str(tuple(x/3 for x in wA)):<20} "
                     f"{wB:>4} {nsq:>8.4f}")

        # Per-class aggregates
        self.log(f"\n{'='*65}\nPer-class aggregates\n{'='*65}")
        self.log(f"\n  {'class':<6} {'N':>3} {'Σ|w|²':>10} "
                 f"{'Σ|wA|²':>10} {'Σ|wB|²':>10} {'Σ|wA|²/N':>10}")
        aggr = {}
        for cls in ['AAA', 'AAB', 'ABB']:
            items = by_class[cls]
            N = len(items)
            sum_sq = sum(x[3] for x in items)
            sum_sqA = sum(sum(a*a for a in x[1])/9.0 for x in items)
            sum_sqB = sum(x[2]**2 for x in items)
            avgA = sum_sqA / N
            aggr[cls] = (N, sum_sq, sum_sqA, sum_sqB, avgA)
            self.log(f"  {cls:<6} {N:>3} {sum_sq:>10.4f} "
                     f"{sum_sqA:>10.4f} {sum_sqB:>10.4f} {avgA:>10.4f}")

        # Test candidate formulas
        book = {'AAA': 13.75, 'AAB': 1.0, 'ABB': 3.5}

        def compare(name, by_cls):
            ref = by_cls['AAA']
            norm = book['AAA'] / ref if ref != 0 else 0
            self.log(f"\n  --- {name} (norm AAA→13.75) ---")
            tot = 0
            for cls in ['AAA', 'AAB', 'ABB']:
                p = by_cls[cls] * norm
                b = book[cls]
                d = (p - b) / b * 100 if b else 0
                tot += abs(d) / 100
                self.log(f"    {cls}: pred={p:>8.4f}  book={b:>6.2f}  dev={d:+7.1f}%")
            return tot

        self.log(f"\n{'='*65}\nCandidate M_i formulas\n{'='*65}")

        cands = {
            'Σ|w|²': {c: aggr[c][1] for c in aggr},
            'Σ|wA|²': {c: aggr[c][2] for c in aggr},
            'Σ|wB|²': {c: aggr[c][3] for c in aggr},
            '(Σ|wA|² + 1)': {c: aggr[c][2] + 1 for c in aggr},
            '1/(Σ|w|²+ε)': {c: 1/(aggr[c][1]+0.01) for c in aggr},
            'N·c^k (c-weighted count per class)': {
                'AAA': 1*1, 'AAB': 6*2, 'ABB': 3*4
            },
            'N (plain hinge count)': {'AAA': 1, 'AAB': 6, 'ABB': 3},
            '1/N': {'AAA': 1, 'AAB': 1/6, 'ABB': 1/3},
            'N² (square hinge count)': {'AAA': 1, 'AAB': 36, 'ABB': 9},
            '1/N²': {'AAA': 1, 'AAB': 1/36, 'ABB': 1/9},
        }

        best_name, best_dev = None, float('inf')
        for name, vals in cands.items():
            d = compare(name, vals)
            if d < best_dev:
                best_dev, best_name = d, name

        self.log(f"\n  BEST: {best_name}, total % dev = {best_dev*100:.2f}%")
        self.check("Best route total dev < 5%", best_dev < 0.05)
        self.check("Best route total dev < 50%", best_dev < 0.5)

        # Summary
        self.log(f"\n{'='*65}\nSUMMARY\n{'='*65}")
        self.log(f"""
  Schubert/Plücker T-weights tested as source of M_i.

  Per-class weight magnitudes computed on Gr(3,5) for SU(3)×SU(2):
    AAA: wA=(0,0,0) (singlet), wB∈{{0,±2}}
    AAB: wA ≠ 0, wB∈{{±1}}
    ABB: wA ≠ 0, wB=0 (B-pair sums to 0)

  Best candidate: {best_name} (tot dev {best_dev*100:.2f}%)

  Verdict:
    If < 5% match → W3 closed (book M_i derives from T-weights).
    If > 50% → Schubert/weight approach fails, need deeper route:
      - Dolbeault cohomology weights
      - Equivariant Chern class integrals
      - Fubini-Study metric-induced measure on Gr(3,5)
""")


if __name__ == "__main__":
    EXP_FND_037().execute()
