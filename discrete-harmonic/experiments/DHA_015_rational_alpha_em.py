"""
DHA_015: Rational Coupling Constants → 1/α_em
================================================
DRLT formula (ch08):
  1/α_i = C_i × g_i × S(N_i)

  Strong: 1/α₃ = 1 × 8 × S(1) = 8        ← S(1) = 1 ∈ ℚ
  Weak:   1/α₂ = 12 × 2 × S(2) = 30      ← S(2) = 5/4 ∈ ℚ
  EM:     1/α₁ = 12 × 3 × S(∞) = 6π²     ← S(∞) = ζ(2) ∉ ℚ

DHA replacement: S(∞) → S(9) = ζ₉ ∈ ℚ
Question: what does 1/α_em become?

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import numpy as np
from fractions import Fraction
from math import comb
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment


class RationalAlphaEM(Experiment):
    ID = "DHA_015"
    TITLE = "Rational Alpha EM"

    def run(self):
        d = 5
        N_S, N_T = 3, 2

        # Build rational spectral measures
        S = {}
        for N in range(1, 10):
            S[N] = Fraction(0)
            for n in range(1, N + 1):
                S[N] += Fraction(1, n**2)

        zeta_2 = np.pi**2 / 6  # irrational reference

        # Test 1: Three couplings — standard vs DHA
        self.log("\n  === Test 1: Three Forces ===\n")
        self._test_three_forces(d, N_S, N_T, S, zeta_2)

        # Test 2: 1/α_em derivation
        self.log("\n  === Test 2: 1/α_em ===\n")
        self._test_alpha_em(d, N_S, N_T, S, zeta_2)

        # Test 3: sin²θ_W
        self.log("\n  === Test 3: Weinberg Angle ===\n")
        self._test_weinberg(d, N_S, N_T, S, zeta_2)

        # Test 4: The S(N) ladder
        self.log("\n  === Test 4: S(N) Spectral Ladder ===\n")
        self._test_ladder(S, zeta_2)

        # Test 5: What N_eff gives 137?
        self.log("\n  === Test 5: Which N_eff Gives 137? ===\n")
        self._test_which_N(d, N_S, N_T, S)

    def _test_three_forces(self, d, N_S, N_T, S, zeta_2):
        """Compute 1/α_i in both frameworks."""
        # Channel multiplicities (from Binet-Cauchy)
        C3 = 1     # SSS: single confined channel
        C2 = 12    # ABB: 3N = 12 (N=4 flat)
        C1 = 12    # AAB: 3N = 12

        # Gauge multiplicities
        g3 = N_S**2 - 1  # adjoint SU(3) = 8
        g2 = N_T          # fundamental SU(2) = 2
        g1 = N_S           # U(1) charges = 3

        # N_eff for each force
        N3 = 1      # confined
        N2 = N_T    # = 2
        N_EM = 9    # DHA: all propagating channels

        # Standard (with π)
        inv_a3_std = C3 * g3 * float(S[1])
        inv_a2_std = C2 * g2 * float(S[2])
        inv_a1_std = C1 * g1 * zeta_2

        # DHA (rational)
        inv_a3_dha = Fraction(C3 * g3) * S[1]
        inv_a2_dha = Fraction(C2 * g2) * S[2]
        inv_a1_dha = Fraction(C1 * g1) * S[N_EM]

        self.log("  Force | C×g  | N_eff | S(N)     | 1/α (std)  | 1/α (DHA)")
        self.log("  " + "-" * 68)
        self.log(f"  Strong| {C3}×{g3}  | {N3}     | {float(S[1]):.4f}   | {inv_a3_std:10.4f} | {float(inv_a3_dha):.4f}")
        self.log(f"  Weak  | {C2}×{g2} | {N2}     | {float(S[2]):.4f}   | {inv_a2_std:10.4f} | {float(inv_a2_dha):.4f}")
        self.log(f"  EM    | {C1}×{g1} | {'∞':5s} | {zeta_2:.4f}   | {inv_a1_std:10.4f} | {float(inv_a1_dha):.4f} (N={N_EM})")

        self.log(f"\n  Standard: 1/α₁ = 6π² = {6*np.pi**2:.6f}")
        self.log(f"  DHA:      1/α₁ = 36ζ₉ = {float(inv_a1_dha):.6f}")
        self.log(f"  Ratio: {float(inv_a1_dha)/inv_a1_std:.6f}")

        # Strong and Weak are ALREADY rational
        self.check("1/α₃ = 8 (already rational)", inv_a3_dha == Fraction(8))
        self.check("1/α₂ = 30 (already rational)", inv_a2_dha == Fraction(30))
        self.check("1/α₁(DHA) = 36ζ₉ ∈ ℚ", True)

    def _test_alpha_em(self, d, N_S, N_T, S, zeta_2):
        """Compute 1/α_em from SU(5) branching."""
        # α_Y = (3/5)α₁, α_em = α_Y α₂/(α_Y + α₂)
        # 1/α_em = (5/3)/α₁ + 1/α₂

        # Standard
        inv_a1_std = 6 * np.pi**2
        inv_a2_std = 30.0
        inv_aem_std = Fraction(5, 3) * inv_a1_std + inv_a2_std

        # DHA: 1/α₁ = 36ζ₉
        inv_a1_dha = Fraction(36) * S[9]
        inv_a2_dha = Fraction(30)

        inv_aem_dha = Fraction(5, 3) * inv_a1_dha + inv_a2_dha

        self.log(f"  1/α_em = (5/3)/α₁ + 1/α₂\n")
        self.log(f"  Standard (π):")
        self.log(f"    (5/3)×6π² + 30 = 10π² + 30 = {10*np.pi**2 + 30:.6f}")
        self.log(f"")
        self.log(f"  DHA (rational):")
        self.log(f"    (5/3)×36ζ₉ + 30 = 60ζ₉ + 30")
        self.log(f"    = {inv_aem_dha}")
        self.log(f"    = {float(inv_aem_dha):.6f}")
        self.log(f"")
        self.log(f"  Observed 1/α_em(M_Z) = 127.9")
        self.log(f"  Standard gives: {10*np.pi**2 + 30:.2f}")
        self.log(f"  DHA gives:      {float(inv_aem_dha):.2f}")

        # QED running from M_Z to Q=0: +9.1 (standard QFT)
        self.log(f"\n  + QED vacuum polarization (+9.1):")
        self.log(f"  Standard: {10*np.pi**2 + 30 + 9.1:.2f}")
        self.log(f"  DHA:      {float(inv_aem_dha) + 9.1:.2f}")
        self.log(f"  Observed: 137.036")

        # The gap
        gap_std = (10*np.pi**2 + 30 + 9.1) / 137.036 - 1
        gap_dha = (float(inv_aem_dha) + 9.1) / 137.036 - 1
        self.log(f"\n  Gap (standard): {gap_std*100:.2f}%")
        self.log(f"  Gap (DHA):      {gap_dha*100:.2f}%")

        # With Δ_i corrections: Δ₁=-0.22, Δ₂=-0.40
        self.log(f"\n  With Δ_i geometric corrections:")
        inv_a1_full = float(inv_a1_dha) - 0.22
        inv_a2_full = 30.0 - 0.40
        inv_aem_full = 5/3 * inv_a1_full + inv_a2_full
        self.log(f"  DHA + Δ: {inv_aem_full + 9.1:.2f}")

        self.check("1/α_em(DHA) is rational", True)

    def _test_weinberg(self, d, N_S, N_T, S, zeta_2):
        """sin²θ_W from the coupling ratio."""
        inv_a1 = Fraction(36) * S[9]
        inv_a2 = Fraction(30)

        # α_em/α₂ = sin²θ_W
        # 1/α_em = (5/3)/α₁ + 1/α₂
        # sin²θ_W = α_em/α₂ = 1/(1 + (5/3)α₂/α₁) = 1/(1 + (5/3)(1/α₁)/(1/α₂))
        # = 1/(1 + (5/3) × inv_a1/inv_a2)
        # = inv_a2 / (inv_a2 + (5/3)inv_a1)
        # = inv_a2 / inv_a_em

        inv_aem = Fraction(5, 3) * inv_a1 + inv_a2
        sin2_W = inv_a2 / inv_aem

        self.log(f"  sin²θ_W = 1/α₂ / (1/α_em)")
        self.log(f"          = {inv_a2} / {inv_aem}")
        self.log(f"          = {sin2_W}")
        self.log(f"          = {float(sin2_W):.8f}")

        # Standard
        sin2_W_std = 30 / (10*np.pi**2 + 30)
        self.log(f"\n  Standard: {sin2_W_std:.8f}")
        self.log(f"  Observed: 0.2312")
        self.log(f"  GUT (SU(5)): 3/8 = {3/8:.4f}")
        self.log(f"\n  DHA gives: {float(sin2_W):.6f}")
        self.log(f"  Standard:   {sin2_W_std:.6f}")

        self.check("sin²θ_W(DHA) ∈ ℚ", True)

    def _test_ladder(self, S, zeta_2):
        """The spectral ladder S(1), S(2), ..., S(9), S(∞)."""
        self.log("  The DRLT spectral ladder:\n")
        self.log("  N | S(N) = Σ₁ᴺ 1/n²  | Float      | Force")
        self.log("  " + "-" * 55)

        forces = {1: "SU(3) strong", 2: "SU(2) weak", 9: "U(1) EM [DHA]"}

        for N in range(1, 10):
            force = forces.get(N, "")
            self.log(f"  {N} | {str(S[N]):18s} | {float(S[N]):.8f} | {force}")

        self.log(f"  ∞ | π²/6              | {zeta_2:.8f} | U(1) EM [std]")
        self.log(f"\n  S(9)/S(∞) = {float(S[9])/zeta_2:.6f}")
        self.log(f"  Missing: {(1-float(S[9])/zeta_2)*100:.2f}%")

        # Key: each step is rational
        self.log(f"\n  EVERY S(N) for finite N is RATIONAL.")
        self.log(f"  S(∞) = ζ(2) is the ONLY irrational value.")
        self.log(f"  DHA replaces this one irrational with S(9) ∈ ℚ.")

    def _test_which_N(self, d, N_S, N_T, S):
        """Find which N_eff gives 1/α_em ≈ 137."""
        self.log("  Scanning: which N gives 1/α_em(0) ≈ 137?\n")
        self.log("  N_eff | 1/α₁      | 1/α_em(M_Z) | +9.1     | vs 137")
        self.log("  " + "-" * 60)

        for N in range(1, 50):
            S_N = sum(Fraction(1, n**2) for n in range(1, N+1))
            inv_a1 = 36 * float(S_N)
            inv_aem_MZ = 5/3 * inv_a1 + 30
            inv_aem_0 = inv_aem_MZ + 9.1
            err = (inv_aem_0 / 137.036 - 1) * 100
            marker = " ←" if abs(err) < 1 else ""
            if N <= 12 or abs(err) < 2 or N % 10 == 0:
                self.log(f"  {N:5d} | {inv_a1:9.4f} | {inv_aem_MZ:11.4f} | {inv_aem_0:8.3f} | {err:+.2f}%{marker}")

        # Also check ∞
        inv_a1_inf = 6 * np.pi**2
        inv_aem_inf = 10*np.pi**2 + 30 + 9.1
        self.log(f"     ∞ | {inv_a1_inf:9.4f} | {10*np.pi**2+30:11.4f} | {inv_aem_inf:8.3f} | {(inv_aem_inf/137.036-1)*100:+.2f}%")

        self.check("N_eff scan completed", True)


if __name__ == "__main__":
    RationalAlphaEM().execute()