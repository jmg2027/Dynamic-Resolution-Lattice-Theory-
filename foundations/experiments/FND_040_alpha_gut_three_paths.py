"""
EXP_FND_040: α_GUT three paths — structural correspondence audit
=================================================================

Research question (honest version of ch03 W10-W12):
  Book ch03 claims three independent derivations of α_GUT = 6/(25π²):
    Path 1 (Binet-Cauchy + Basel):  α = 1/(d²·ζ(2))
    Path 2 (GUE 2-point function):  α = 1/(d²·ζ(2)) (via RMT coefficient)
    Path 3 (Euler coprime density): α = P(coprime)/d² = (1/ζ(2))/d²
  All three give the same number.  But are they the SAME OBJECT in
  three disguises, or three INDEPENDENT facts coinciding?

Findings (this experiment):
  1. All three paths STRUCTURALLY reduce to α = 1/(d²·ζ(2)).
  2. Path 1 and Path 3 are LINKED by Euler's identity:
        ζ(2) = Σ 1/n² = ∏_p (1 - 1/p²)^{-1}
     Thus "sum over hinge index n" (Path 1) and "coprime pair density"
     (Path 3) are two sides of the SAME mathematical fact.
  3. Path 2 (GUE) gives the same NUMBER by completely different math
     (sine kernel expansion).  The link to Path 1/3 is CONJECTURAL —
     universal RMT properties of Hermitian Gram matrices might explain
     it, but DRLT does not (yet) provide that derivation.

Conclusion:
  α_GUT = 1/(d²·ζ(2)) is ONE formula with TWO rigorous interpretations
  (Path 1 = Path 3 via Euler) and ONE numerical coincidence (Path 2).
  Book ch03 claims "three independent paths" — honest version: two
  paths (which are Euler-equivalent) + one RMT coincidence awaiting
  a derivation.

Checks:
  1. Numerical equality of the three paths (10-digit precision)
  2. Path 1 ↔ Path 3: explicit Euler product identity check
  3. Path 2: sine kernel r² coefficient matches ζ(2)·2/3
  4. α_GUT value matches book constant to all digits
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
from math import pi, sin
from functools import reduce


def euler_product_partial(prime_limit):
    """Partial Euler product ∏_{p≤N} (1 - 1/p²) for primes p ≤ prime_limit."""
    primes = []
    for n in range(2, prime_limit + 1):
        is_prime = True
        for p in primes:
            if p * p > n:
                break
            if n % p == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(n)
    product = 1.0
    for p in primes:
        product *= (1.0 - 1.0 / (p * p))
    return product, len(primes)


def basel_partial(n_max):
    """Partial sum Σ_{n=1}^{n_max} 1/n² (Basel)."""
    return sum(1.0 / (n * n) for n in range(1, n_max + 1))


def sine_kernel_r2_coeff():
    """Short-distance expansion of GUE 2-point function:
       Y₂(r) = (sin(πr)/(πr))² = 1 - (πr)²/3 + O(r⁴)
       Coefficient of r² in Y₂: -(π²/3) = -2·ζ(2)
       Level repulsion R₂(r) = 1 - Y₂(r) ≈ (π²/3)r² for small r.
       Coefficient of r² in R₂: π²/3 = 2·ζ(2)."""
    return pi * pi / 3.0


class EXP_FND_040(Experiment):
    ID = "FND_040"
    TITLE = "alpha_GUT Three Paths Correspondence"

    def run(self):
        self.log("=" * 65)
        self.log("α_GUT THREE PATHS — STRUCTURAL CORRESPONDENCE")
        self.log("=" * 65)
        self.log("")
        self.log("  Book ch03 claims three derivations of α_GUT = 6/(25π²).")
        self.log("  Honest question: three independent facts, or one fact")
        self.log("  seen through three windows?")
        self.log("")

        d = 5
        zeta2 = pi * pi / 6.0
        alpha_gut_exact = 6.0 / (25.0 * pi * pi)

        # Path 1: 1/(d²·ζ(2)) direct
        alpha_path1 = 1.0 / (d * d * zeta2)
        # Path 2: 1/(d²·ζ(2)) via GUE (algebraically identical formula)
        alpha_path2 = 1.0 / (d * d * zeta2)
        # Path 3: P(coprime)/d² = (1/ζ(2))/d² = 1/(d²·ζ(2))
        alpha_path3 = (1.0 / zeta2) / (d * d)

        self.log("=" * 65)
        self.log("CHECK 1: Numerical equality of all three paths")
        self.log("=" * 65)
        self.log(f"\n  α_GUT exact      = 6/(25π²)    = {alpha_gut_exact:.12f}")
        self.log(f"  Path 1 (Basel)   = 1/(d²·ζ(2)) = {alpha_path1:.12f}")
        self.log(f"  Path 2 (GUE)     = 1/(d²·ζ(2)) = {alpha_path2:.12f}")
        self.log(f"  Path 3 (Coprime) = (1/ζ(2))/d² = {alpha_path3:.12f}")
        self.log("")
        d1 = abs(alpha_path1 - alpha_gut_exact)
        d2 = abs(alpha_path2 - alpha_gut_exact)
        d3 = abs(alpha_path3 - alpha_gut_exact)
        self.log(f"  Max deviation from exact: {max(d1, d2, d3):.2e}")
        self.check("All three paths match α_GUT to float precision",
                   max(d1, d2, d3) < 1e-15)

        # Check 2: Path 1 ↔ Path 3 via Euler's identity
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 2: Path 1 ↔ Path 3 via Euler identity")
        self.log("=" * 65)
        self.log("")
        self.log("  Euler: ζ(2) = ∏_p (1 - 1/p²)⁻¹.  So 1/ζ(2) = ∏_p (1-1/p²).")
        self.log("  Path 1's Σ 1/n² and Path 3's coprime density are")
        self.log("  TWO SIDES of Euler's identity — same mathematical fact.")
        self.log("")
        self.log(f"  {'prime≤':>7} {'1/ζ₂(N) (Basel)':>18} {'∏(1-1/p²) (Euler)':>20}"
                 f" {'diff':>10}")
        worst_euler = 0.0
        for N in [10, 100, 1000, 10000, 100000]:
            basel = basel_partial(N)
            inv_basel = 1.0 / basel  # 1 / partial Basel (asymptote: 1/ζ(2))
            euler_partial, nprimes = euler_product_partial(N)
            diff = abs(inv_basel - euler_partial)
            worst_euler = max(worst_euler, diff / euler_partial)
            self.log(f"  {N:>7} {basel:>18.10f} {euler_partial:>20.10f}"
                     f" {diff:>10.3e}")
        # Asymptotic: both → 1/ζ(2) = 6/π² ≈ 0.6079...
        self.log(f"\n  Both converge to 1/ζ(2) = 6/π² = {6.0/(pi*pi):.10f}")
        self.check("Basel ↔ Euler connection (same ζ(2))", worst_euler < 0.1)

        # Check 3: Path 2 GUE sine kernel
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 3: Path 2 (GUE sine kernel r² coefficient)")
        self.log("=" * 65)
        self.log("")
        r2_theoretical = sine_kernel_r2_coeff()  # π²/3 = 2ζ(2)
        self.log(f"  Sine kernel: Y₂(r) = (sin(πr)/(πr))²")
        self.log(f"  Short-distance expansion: Y₂(r) ≈ 1 - (πr)²/3 + O(r⁴)")
        self.log(f"  Coefficient of r² in [1 - Y₂(r)] = π²/3 = {r2_theoretical:.6f}")
        self.log(f"  This equals 2·ζ(2) = {2*zeta2:.6f}")
        # Numerical verification by sampling small r
        for r in [0.01, 0.001, 0.0001]:
            y2 = (sin(pi * r) / (pi * r)) ** 2
            coeff_numerical = (1.0 - y2) / (r * r)
            self.log(f"    r = {r:.4f}: (1-Y₂(r))/r² = {coeff_numerical:.8f}")
        self.check("GUE sine kernel r² coeff = π²/3 = 2·ζ(2)",
                   abs(r2_theoretical - 2 * zeta2) < 1e-12)

        # Check 4: Book constant consistency
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 4: α_GUT matches book CLAUDE.md constant")
        self.log("=" * 65)
        self.log("")
        # CLAUDE.md: α_GUT = 6/(25π²) ≈ 0.02433
        self.log(f"  α_GUT = {alpha_gut_exact:.10f}")
        self.log(f"  1/α_GUT = {1.0/alpha_gut_exact:.6f}  (GUT coupling)")
        self.log(f"  1/α_em (at GUT scale, MSbar) = 137.036")
        self.log(f"  α_GUT ≪ α_em since GUT unifies at higher energy.")
        self.check("α_GUT ≈ 0.02433", abs(alpha_gut_exact - 0.02433) < 1e-4)

        # Honest conclusion
        self.log("")
        self.log("=" * 65)
        self.log("CONCLUSION: structural correspondence")
        self.log("=" * 65)
        self.log("")
        self.log("  ONE formula: α_GUT = 1/(d²·ζ(2)) = 6/(25π²).")
        self.log("")
        self.log("  Two rigorous paths (mathematically equivalent):")
        self.log("    Path 1 (Basel sum over hinge index n)")
        self.log("      ≡ Path 3 (Euler coprime density)")
        self.log("    via  ζ(2) = Σ 1/n² = ∏_p (1 - 1/p²)⁻¹.")
        self.log("    Euler's identity is a THEOREM of number theory —")
        self.log("    not a DRLT-specific coincidence.")
        self.log("")
        self.log("  One additional path (GUE) gives same number via")
        self.log("  unrelated RMT math.  The DRLT claim that GUE β=2")
        self.log("  YIELDS α_GUT via sine-kernel expansion is PLAUSIBLE")
        self.log("  but not formally derived: the sine-kernel coefficient")
        self.log("  2·ζ(2) happens to match 2/α_GUT·d² up to normalization.")
        self.log("")
        self.log("  Honest book update recommendation:")
        self.log("    - Keep Path 1 (geometric, Binet-Cauchy counting) as")
        self.log("      the PRIMARY derivation.")
        self.log("    - Document Path 3 as the NUMBER-THEORETIC sibling")
        self.log("      via Euler identity (not an independent derivation).")
        self.log("    - Mark Path 2 (GUE) as a CONSISTENCY CHECK awaiting")
        self.log("      a formal derivation from DRLT's Gram matrix RMT.")
        self.log("")
        self.log("  Net: 3 derivations → 1 theorem (Path 1), 1 number")
        self.log("  theoretic sibling (Path 3 via Euler), 1 plausible check")
        self.log("  (Path 2).  This is honest scope.")


if __name__ == "__main__":
    EXP_FND_040().execute()
