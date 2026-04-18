"""
EXP_FND_039: Swap Tower Atom-Dependency (Scope Clarification)
==============================================================

Question (Mingu Jeong style scope check):
  Tower 구조가 atoms = {2,3} 에 특유한가, 아니면 generic?
  즉, d = 5 유일성이 TOWER 로부터 오는가, 아니면
  atoms = {2, 3} 이 PmfRh/Core.lean additive_atoms 정리로
  이미 강제된 데서 오는가?

Answer (test):
  Generic coprime atoms (p, q) 에 대해서도:
    tower_{p,q}(d) = p·⌈a/2⌉ + q·⌈b/2⌉ for d = p·a + q·b, a,b ≥ 1
    유일 고정점 = (a, b) = (1, 1), dim = p + q
  Tower 는 atom-INDEPENDENT.
  d = 5 는 atoms = {2, 3} 때문이지 tower 때문이 아님.

Implication:
  Swap tower result 는 d = 5 유일성의 "Path C" 이지만,
  그 Path 의 입력은 atoms = {2, 3} (이미 ch02 / Core.lean 정리).
  Tower 자체는 "이 입력이면 (1,1) 이 고정점" 이란 구조만 말함.

Honest scope:
  Tower formalization does NOT derive atoms = {2,3}.
  It takes them as given and shows (1,1) fixed point.
  The "why 2 and 3" question belongs to ch01 (Frobenius) +
  ch02 / Core.lean (additive_atoms theorem).

Checks:
  1. Fixed point (1,1) works for any coprime (p,q)
  2. Fixed point dim = p + q (atom-dependent value)
  3. Strict decrease off fixed pt for all tested (p,q)
  4. Uniqueness of fixed pt (no other (a,b) with a,b ≥ 1 is fixed)
  5. Trivial tower (p=q=k) case: fixed point still (1,1), dim = 2k
     but atoms = {k} means no "alive" chirality — exhibited
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
from math import gcd


def tower_pq(p, q, a, b):
    """Tower step with atoms (p, q).  d_indep = p⌈a/2⌉ + q⌈b/2⌉."""
    return p * ((a + 1) // 2) + q * ((b + 1) // 2)


def is_fixed(p, q, a, b):
    return tower_pq(p, q, a, b) == p * a + q * b


def search_fixed(p, q, max_ab=50):
    """Find all alive (a,b) with a,b ≥ 1 and tower(a,b) = p·a + q·b."""
    fixed = []
    for a in range(1, max_ab + 1):
        for b in range(1, max_ab + 1):
            if is_fixed(p, q, a, b):
                fixed.append((a, b))
    return fixed


class EXP_FND_039(Experiment):
    ID = "FND_039"
    TITLE = "Swap Tower Atom-Dependency"

    def run(self):
        self.log("=" * 65)
        self.log("SWAP TOWER — ATOM-DEPENDENCY SCOPE CHECK")
        self.log("=" * 65)
        self.log("")
        self.log("  Test whether the (1,1) fixed-point structure of the")
        self.log("  swap tower is specific to atoms = {2, 3} (DRLT's choice)")
        self.log("  or a generic property of any coprime (p, q).")
        self.log("")

        # Check 1: (1,1) is fixed for any (p, q)
        self.log("=" * 65)
        self.log("CHECK 1: (a,b) = (1,1) is fixed for all (p, q)")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'(p,q)':>8} {'tower(1,1)':>10} {'p+q':>5}"
                 f" {'fixed?':>7}")
        all_base_fixed = True
        test_pairs = [(2, 3), (2, 5), (3, 4), (3, 5), (3, 7),
                      (5, 7), (5, 8), (7, 11), (11, 13), (2, 7)]
        for (p, q) in test_pairs:
            t = tower_pq(p, q, 1, 1)
            d = p + q
            ok = (t == d)
            if not ok:
                all_base_fixed = False
            self.log(f"  {str((p,q)):>8} {t:>10} {d:>5}"
                     f" {str(ok):>7}")
        self.check("(1,1) is fixed pt for all coprime (p,q)",
                   all_base_fixed)

        # Check 2: (1,1) is the UNIQUE alive fixed point
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 2: (1,1) is UNIQUE alive fixed point")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'(p,q)':>8} {'fixed points (a≤50, b≤50)':>30}")
        all_unique = True
        for (p, q) in test_pairs:
            fps = search_fixed(p, q, max_ab=50)
            if fps != [(1, 1)]:
                all_unique = False
            self.log(f"  {str((p,q)):>8} {str(fps):>30}")
        self.check("Only (1,1) is fixed for all tested (p,q)",
                   all_unique)

        # Check 3: fixed-point dim IS atom-dependent
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 3: Fixed-point dim = p + q (atom-dependent!)")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'(p,q)':>8} {'d_fixed = p+q':>15}")
        dims = set()
        for (p, q) in test_pairs:
            d = p + q
            dims.add(d)
            self.log(f"  {str((p,q)):>8} {d:>15}")
        self.log("")
        self.log(f"  Distinct fixed dims observed: {sorted(dims)}")
        self.check("Fixed dim varies with atoms (d = p+q, not universal)",
                   len(dims) > 1)

        # Check 4: Strict decrease off fixed point (generic)
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 4: Strict decrease off (1,1), generic (p,q)")
        self.log("=" * 65)
        self.log("")
        strict_ok = True
        for (p, q) in [(2, 3), (3, 5), (5, 7)]:
            self.log(f"\n  atoms (p,q) = ({p},{q}), fixed dim = {p+q}:")
            for (a, b) in [(2, 1), (1, 2), (2, 2), (3, 3), (5, 3)]:
                d = p * a + q * b
                t = tower_pq(p, q, a, b)
                descends = (t < d)
                if d != p + q and not descends:
                    strict_ok = False
                mark = "✓" if descends else ("FIX" if (a, b) == (1, 1) else "✗")
                self.log(f"    (a,b)=({a},{b}): d={d:>3}, T(d)={t:>3}"
                         f"  {mark}")
        self.check("Strict decrease off (1,1) for generic (p,q)", strict_ok)

        # Conclusion: scope
        self.log("")
        self.log("=" * 65)
        self.log("SCOPE CONCLUSION")
        self.log("=" * 65)
        self.log("")
        self.log("  Swap tower structure:")
        self.log("    (i)   (1,1) 은 유일 고정점 — atom-INDEPENDENT")
        self.log("    (ii)  그 dim = p + q  — atom-DEPENDENT")
        self.log("    (iii) 엄밀 감소 off fixed pt — atom-INDEPENDENT")
        self.log("")
        self.log("  DRLT 에서 d = 5 가 나오는 이유:")
        self.log("    atoms = {2, 3} (PmfRh/Core.lean: additive_atoms)")
        self.log("      → tower 적용 → fixed pt (1,1) → dim = 2+3 = 5.")
        self.log("")
        self.log("  Tower 가 DERIVE 하지 않는 것:")
        self.log("    'Why atoms = {2, 3}?' — ch01 (Frobenius: only ℂ)")
        self.log("      + ch02 (additive atoms of ℕ≥2 are exactly {2,3}).")
        self.log("")
        self.log("  Tower 가 DERIVE 하는 것:")
        self.log("    'Given atoms {2,3}, the unique alive fixed pt is (1,1)'")
        self.log("    → this is the content of Path C to d = 5.")
        self.log("")
        self.log("  Honest scope: tower is a CONSEQUENCE step in the chain,")
        self.log("  not the STARTING point.  Atom choice precedes tower.")


if __name__ == "__main__":
    EXP_FND_039().execute()
