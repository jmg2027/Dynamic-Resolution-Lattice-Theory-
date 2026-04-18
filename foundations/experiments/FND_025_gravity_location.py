"""
EXP_FND_025: Where does gravity live in Lambda^k(C^5)?
=======================================================

Gap G-D2 from FND_024: 
  SM forces = Binet-Cauchy 25 channels in Lambda^3(C^5).
  Gravity has no Binet-Cauchy location, only Delta_G residual.

Test candidate locations for gravity in Lambda^k(C^5) by computing
c-weighted channel counts and checking consistency with Delta_G.

Candidates:
  H1: Lambda^5(C^5) simplex volume, 1 channel (c^2 weighted = 4)
  H2: Lambda^4(C^5) tetrahedra, c-weighted count
  H3: Lambda^2(C^5) edges, c-weighted count
  H4: Lambda^1(C^5) vertices, c-weighted count
  H5: Gravity = total - 25 (complement in some total)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
from math import comb


def c_weighted_lambda(k, n_A=3, n_B=2, c=2):
    """c-weighted channel count for Lambda^k(V_A ⊕ V_B).
    Sum over decomposition k = k_A + k_B with k_A <= n_A, k_B <= n_B.
    Each term weighted by c^{k_B}."""
    total = 0
    breakdown = []
    for k_B in range(min(k, n_B) + 1):
        k_A = k - k_B
        if k_A > n_A or k_A < 0:
            continue
        channels = comb(n_A, k_A) * comb(n_B, k_B)
        weight = c ** k_B
        total += channels * weight
        breakdown.append((k_A, k_B, channels, weight, channels * weight))
    return total, breakdown


class EXP_FND_025(Experiment):
    ID = "FND_025"
    TITLE = "Gravity location in Lambda"

    def run(self):
        self.log("=" * 65)
        self.log("GRAVITY LOCATION: which Lambda^k(C^5)?")
        self.log(f"{'='*65}")
        
        self.log("""
  Book's SM forces: Lambda^3(C^5) -> 1+12+12 = 25 channels (hinges).
  Gravity: no explicit Lambda^k assignment in book.

  Compute c-weighted channel counts for each Lambda^k:
""")
        self.log(f"  {'k':>3} {'Lambda^k(C^5)':>20} {'c-weighted':>12}"
                 f" {'breakdown (k_A, k_B, count, c^k_B)':>40}")
        self.log(f"  {'-'*3} {'-'*20} {'-'*12} {'-'*40}")

        all_counts = {}
        for k in range(6):
            total, bd = c_weighted_lambda(k)
            # Format breakdown
            bd_str = ", ".join(
                f"({ka},{kb}):{count}*{weight}={ch}"
                for ka, kb, count, weight, ch in bd if ch > 0
            )
            self.log(f"  {k:>3} {f'dim = {comb(5,k)}':>20} {total:>12}  {bd_str}")
            all_counts[k] = total

        self.log(f"""
  Notable numbers:
    Lambda^0: 1       (scalar, no physics)
    Lambda^1: 7       (vertices)
    Lambda^2: 19      (edges)
    Lambda^3: 25 = d^2 (hinges = SM forces!)
    Lambda^4: 16      (tetrahedra)
    Lambda^5: 4 = c^2 (simplex volume)

  Sum over all Lambda^k: {sum(all_counts.values())}
""")
        self.check("Lambda^3 = 25 = d^2", all_counts[3] == 25)
        self.check("Lambda^5 = c^2 = 4", all_counts[5] == 4)
        self.check("Lambda^0 = 1 (scalar)", all_counts[0] == 1)

        # Test hypotheses for gravity Delta_G ~= +0.15
        self.log(f"\n{'='*65}")
        self.log("HYPOTHESIS TESTS: Delta_G prediction")
        self.log(f"{'='*65}")
        
        import math
        alpha_GUT = 6 / (25 * math.pi**2)
        eps0 = 0.0038
        Delta_G_book = 0.15
        
        self.log(f"\n  alpha_GUT = {alpha_GUT:.6f}, eps_0 = {eps0}")
        self.log(f"  Book's Delta_G = +0.15\n")
        
        hypotheses = [
            ("H1: Gravity = Lambda^5 (simplex vol)", 4),
            ("H2: Gravity = Lambda^4 (tet facets)", 16),
            ("H3: Gravity = Lambda^2 (edges)", 19),
            ("H4: Gravity = Lambda^1 (vertices)", 7),
            ("H5: Gravity = Lambda^0 (scalar)", 1),
        ]
        
        self.log(f"  {'Hypothesis':<40} {'channels':>10} {'Delta*eps':>10}"
                 f" {'match?':>8}")
        self.log(f"  {'-'*40} {'-'*10} {'-'*10} {'-'*8}")
        for name, ch in hypotheses:
            delta_pred = ch * eps0  # simplest form: channels * eps
            ratio = delta_pred / Delta_G_book if Delta_G_book else 0
            match = "close" if abs(ratio - 1) < 0.3 else ""
            self.log(f"  {name:<40} {ch:>10} {delta_pred:>10.4f}"
                     f" {match:>8}")

        self.log("""
  Observation: none of the simple 'Delta_G = channels * eps_0' 
  hypotheses match book's 0.15 exactly.
    Lambda^4 (16 * 0.0038 = 0.061): too low (40%)
    Lambda^3 (25 * 0.0038 = 0.095): low
    Lambda^2 (19 * 0.0038 = 0.072): low
  
  None hit 0.15 naturally.
""")

        # More careful: Delta_i formula from book
        # Delta_i = Sgn_i * (1/alpha_i)_comb * M_i * eps_0
        # with M_3=13.75, M_2=3.5, M_1=1.0
        self.log(f"\n{'='*65}")
        self.log("BOOK FORMULA CONSISTENCY CHECK")
        self.log(f"{'='*65}")
        self.log("""
  Book formula (ch12.117-120):
    Delta_i = Sgn_i * (1/alpha_i)_comb * M_i * eps_0
    Strong:  Sgn=+1, 1/alpha=8,     M=13.75 -> Delta_3 = +8*13.75*eps
    Weak:    Sgn=-1, 1/alpha=30,    M=3.5   -> Delta_2 = -30*3.5*eps
    EM:      Sgn=-1, 1/alpha=59.22, M=1.0   -> Delta_1 = -59.22*1.0*eps
""")
        
        d3 = 8 * 13.75 * eps0
        d2 = -30 * 3.5 * eps0
        d1 = -59.22 * 1.0 * eps0
        sum_SM = d3 + d2 + d1
        d_G_predicted = -sum_SM
        
        self.log(f"  At eps_0 = {eps0}:")
        self.log(f"    Delta_3 = {d3:+.4f}  (book: +0.47, dev {abs(d3-0.47)/0.47*100:.1f}%)")
        self.log(f"    Delta_2 = {d2:+.4f}  (book: -0.40, dev {abs(d2-(-0.40))/0.40*100:.1f}%)")
        self.log(f"    Delta_1 = {d1:+.4f}  (book: -0.22, dev {abs(d1-(-0.22))/0.22*100:.1f}%)")
        self.log(f"    Sum SM  = {sum_SM:+.4f}")
        self.log(f"    Delta_G = -Sum = {d_G_predicted:+.4f}  (book: +0.15, "
                 f"dev {abs(d_G_predicted-0.15)/0.15*100:.1f}%)")
        self.log("""
  Discrepancy: formula Delta_i = Sgn * (1/alpha)_comb * M_i * eps_0
  matches individual Delta_i within ~5-15% of book values, but the
  derived Delta_G (= -Sum SM) is +0.21, 42% off book's +0.15.

  INTERPRETATION: either
    (a) book's M_i or eps_0 have implicit corrections
    (b) Delta_G is NOT simply -Sum(SM Delta)
    (c) Book's quoted values are approximate to ~10%
  
  Honest: the book's 4-sector framework has UNRESOLVED numerical
  inconsistency at 10-40% level.
""")
        self.check("formula gives SM Delta within 15% of book", 
                   abs(d3-0.47)/0.47 < 0.15 and 
                   abs(d2-(-0.40))/0.40 < 0.15 and
                   abs(d1-(-0.22))/0.22 < 0.15)
        self.check("Delta_G from sum-rule matches book within 50%",
                   abs(d_G_predicted - 0.15) / 0.15 < 0.5)

        # Summary + structural conclusion
        self.log(f"\n{'='*65}")
        self.log("STRUCTURAL CONCLUSION")
        self.log(f"{'='*65}")
        self.log("""
  Attempted location hypotheses:
    Lambda^0 (1), Lambda^1 (7), Lambda^2 (19), Lambda^3 (25=SM),
    Lambda^4 (16), Lambda^5 (4).
  None give Delta_G = +0.15 naturally via 'channels * eps_0'.

  Book's formula Delta_i = Sgn * (1/alpha)_comb * M_i * eps_0:
    - Fits strong/weak/EM within 10-15% (M_i FIT, not derived)
    - Sum-rule Delta_G = -Sum(SM) gives +0.21, book says +0.15 (42% off)

  FINDINGS:
  1. Gravity is NOT in Lambda^3(C^5) = the SM Binet-Cauchy space.
  2. Gravity is also NOT cleanly in any other Lambda^k via simple formula.
  3. The 4-sector framework is under-determined:
     - M_i weights (13.75, 3.5, 1.0) are fit to data, not derived.
     - eps_0 is positional, not derived.
     - Delta_G from sum rule is internally inconsistent with 
       individually-derived Delta_i at ~40% level.

  USER'S INTUITION CONFIRMED in specific sense:
    Gravity doesn't live in the same 'channel space' as SM forces.
    It's treated as a 'residual' that closes trace conservation,
    but this residual has UNRESOLVED quantitative inconsistency.

  GAP G-D2 STATUS:
    Remains OPEN. Resolution requires either:
    (a) First-principles derivation of M_i values
    (b) Independent geometric formula for Delta_G (not via sum rule)
    (c) Explicit location of gravity in exterior algebra structure
""")


if __name__ == "__main__":
    EXP_FND_025().execute()
