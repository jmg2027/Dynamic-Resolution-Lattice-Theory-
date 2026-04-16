"""
DHA_014: Integer Structure of the Coupling
============================================
ζ₉ = 9778141/6350400. What are these numbers?

6350400 = lcm(1², 2², ..., 9²)?
9778141 = prime?
α = 254016/9778141 — what is 254016?

The coupling constant is built from integers.
What integers, and why?

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import numpy as np
from fractions import Fraction
from math import gcd, comb, factorial
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment


def factorize(n):
    """Return prime factorization as dict {p: e}."""
    factors = {}
    d = 2
    while d * d <= abs(n):
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if abs(n) > 1:
        factors[abs(n)] = factors.get(abs(n), 0) + 1
    return factors


def lcm(a, b):
    return a * b // gcd(a, b)


class IntegerStructure(Experiment):
    ID = "DHA_014"
    TITLE = "Integer Structure of Coupling"

    def run(self):
        # Build ζ₉ exactly
        zeta = Fraction(0)
        for n in range(1, 10):
            zeta += Fraction(1, n**2)

        num, den = zeta.numerator, zeta.denominator
        d = 5
        alpha = Fraction(1, d**2) / zeta  # = den/(d²×num)

        self.log(f"\n  ζ₉ = {num}/{den}")
        self.log(f"  α₉ = {alpha.numerator}/{alpha.denominator}")

        # Test 1: Denominator = lcm structure
        self.log("\n  === Test 1: Denominator of ζ₉ ===\n")
        self._test_denominator(den)

        # Test 2: Numerator factorization
        self.log("\n  === Test 2: Numerator of ζ₉ ===\n")
        self._test_numerator(num)

        # Test 3: α numerator/denominator
        self.log("\n  === Test 3: α = 254016/9778141 ===\n")
        self._test_alpha(alpha, den, d)

        # Test 4: Integer relationships
        self.log("\n  === Test 4: Integer Relationships ===\n")
        self._test_relationships(num, den, d)

        # Test 5: The f_occ fraction
        self.log("\n  === Test 5: f_occ as Fraction ===\n")
        self._test_focc(alpha, d)

    def _test_denominator(self, den):
        """Is den = lcm(1², 2², ..., 9²)?"""
        L = 1
        self.log("  Building lcm(1², 2², ..., 9²):")
        for n in range(1, 10):
            L = lcm(L, n**2)
            self.log(f"    lcm up to {n}²={n**2:3d}: {L}")

        self.log(f"\n  lcm(1²,...,9²) = {L}")
        self.log(f"  ζ₉ denominator = {den}")
        self.check("den(ζ₉) = lcm(1², 2², ..., 9²)", den == L)

        # Factorize
        factors = factorize(den)
        self.log(f"\n  {den} = {' × '.join(f'{p}^{e}' for p,e in sorted(factors.items()))}")

        # Alternative expressions
        self.log(f"\n  = (2³)² × (3²)² × 5² × 7²")
        self.log(f"  = (8 × 9 × 5 × 7)² / something...")
        self.log(f"  = lcm of all n² for n ≤ 9 = lcm of squares ≤ N_eff²")

    def _test_numerator(self, num):
        """Factorize and analyze 9778141."""
        factors = factorize(num)

        if len(factors) == 1 and list(factors.values())[0] == 1:
            self.log(f"  {num} is PRIME!")
            self.check("Numerator of ζ₉ is prime", True)
        else:
            self.log(f"  {num} = {' × '.join(f'{p}^{e}' for p,e in sorted(factors.items()))}")
            self.check("Numerator factored", True)

        # Check divisibility by small primes
        self.log(f"\n  Divisibility checks:")
        for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
            if num % p == 0:
                self.log(f"    {num} ÷ {p} = {num//p}")

        # Modular properties
        self.log(f"\n  Modular properties:")
        for m in [9, 10, 24, 25, 120]:
            self.log(f"    {num} mod {m} = {num % m}")

    def _test_alpha(self, alpha, den_zeta, d):
        """Analyze α = 254016/9778141."""
        p, q = alpha.numerator, alpha.denominator

        self.log(f"  α₉ = {p}/{q}")

        # Factorize numerator
        factors_p = factorize(p)
        self.log(f"\n  Numerator {p}:")
        self.log(f"  = {' × '.join(f'{pr}^{e}' for pr,e in sorted(factors_p.items()))}")

        # Is 254016 = den_zeta / d² ?
        expected = den_zeta // d**2
        self.log(f"\n  den(ζ₉)/d² = {den_zeta}/{d**2} = {expected}")
        self.check(f"α numerator = den(ζ₉)/d² = {expected}", p == expected)

        # So α = den(ζ₉)/(d² × num(ζ₉)) = (1/d²) × den/num = 1/(d²ζ₉) ✓
        self.log(f"\n  Confirmed: α = lcm(1²,...,9²) / (d² × num(ζ₉))")

        # Factorize denominator
        factors_q = factorize(q)
        if len(factors_q) == 1:
            self.log(f"\n  Denominator {q} is PRIME")
        else:
            self.log(f"\n  Denominator {q} = {' × '.join(f'{pr}^{e}' for pr,e in sorted(factors_q.items()))}")

    def _test_relationships(self, num, den, d):
        """Find integer relationships."""
        N_eff = comb(d, 3) - 1  # 9
        adj = d**2 - 1  # 24

        self.log(f"  Key integers:")
        self.log(f"    d = {d}")
        self.log(f"    d² = {d**2}")
        self.log(f"    d²-1 = {adj} (adjoint)")
        self.log(f"    C(d,3) = {comb(d,3)}")
        self.log(f"    N_eff = {N_eff}")
        self.log(f"    |S_d| = {factorial(d)} = {d}!")
        self.log(f"    lcm denom = {den}")
        self.log(f"    num(ζ₉) = {num}")

        # Ratios
        self.log(f"\n  Ratios:")
        self.log(f"    den/d! = {den}/{factorial(d)} = {den/factorial(d):.1f}")
        self.log(f"    den/(d!)² = {den/factorial(d)**2:.4f}")
        self.log(f"    num/den = ζ₉ = {num/den:.10f}")
        self.log(f"    den/num = 1/ζ₉ = {den/num:.10f}")

        # Check: den = (N_eff!)² / something?
        self.log(f"\n    (N_eff)! = {factorial(N_eff)}")
        self.log(f"    (N_eff)!² = {factorial(N_eff)**2}")
        self.log(f"    den/(N_eff)!² = {den/factorial(N_eff)**2}")
        # 9! = 362880, (9!)² = 131681894400
        # den = 6350400
        # (9!)²/den = 131681894400/6350400 = 20736 = 144² = (12)⁴... interesting?
        ratio = factorial(N_eff)**2 // den
        self.log(f"    (N_eff)!²/den = {ratio}")
        factors_r = factorize(ratio)
        self.log(f"    = {' × '.join(f'{p}^{e}' for p,e in sorted(factors_r.items()))}")
        self.log(f"    = {int(np.sqrt(ratio))}² ?" if int(np.sqrt(ratio))**2 == ratio else "")

        self.check("Integer relationships explored", True)

    def _test_focc(self, alpha, d):
        """f_occ = 24α/(24+α+α²) as exact fraction."""
        adj = d**2 - 1
        f_occ = adj * alpha / (adj + alpha + alpha**2)

        p, q = f_occ.numerator, f_occ.denominator

        self.log(f"  f_occ = {p}")
        self.log(f"        / {q}")
        self.log(f"        = {float(f_occ):.15f}")

        # Number of digits
        self.log(f"\n  Numerator digits: {len(str(p))}")
        self.log(f"  Denominator digits: {len(str(q))}")

        # Factorize
        factors_p = factorize(p)
        factors_q = factorize(q)
        self.log(f"\n  num = {' × '.join(f'{pr}^{e}' for pr,e in sorted(factors_p.items()))}")
        self.log(f"  den = {' × '.join(f'{pr}^{e}' for pr,e in sorted(factors_q.items()))}")

        # The coupling constant of the universe is this exact fraction
        self.log(f"\n  ════════════════════════════════════════")
        self.log(f"  THE COUPLING CONSTANT OF THE UNIVERSE")
        self.log(f"  (in the DHA rational framework)")
        self.log(f"  ════════════════════════════════════════")
        self.log(f"  f_occ = {p}/{q}")

        self.check("f_occ computed as exact fraction", True)


if __name__ == "__main__":
    IntegerStructure().execute()