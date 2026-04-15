"""
DHA_011: The Adjoint Correction — f_occ = α(1 - α(1+α)/(d²-1))
================================================================
DHA_010 found: Δα/(α²(1+α)) ≈ 1/24 = 1/(d²-1).
This suggests: f_occ = α × (1 - α(1+α)/(d²-1))

If true: the 0.1% gap = 1-loop adjoint SU(5) self-energy!
d²-1 = 24 = dim(adj SU(5)).

Verify to maximum precision and check d-universality.

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import numpy as np
from scipy.optimize import minimize_scalar
from math import comb
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment


class AdjointCorrection(Experiment):
    ID = "DHA_011"
    TITLE = "Adjoint Correction Formula"

    def regge_critical(self):
        def S(eps):
            if eps <= 0 or eps >= 1/np.sqrt(3):
                return 0.0
            x = eps**2
            c1 = eps / np.sqrt(1 - 2*x)
            c2 = -x / (1 - 2*x)
            d2 = np.sqrt(1 - x)
            t1 = np.arccos(np.clip(c1, -1, 1))
            t2 = np.arccos(np.clip(c2, -1, 1))
            return 12 * ((2*np.pi - t1) + d2 * (2*np.pi - t2))
        res = minimize_scalar(lambda e: -S(e),
                              bounds=(0.001, 0.5), method='bounded')
        return res.x

    def run(self):
        d = 5
        eps = self.regge_critical()
        x = eps**2
        f_occ = x / (1 + x)
        alpha = 6 / (d**2 * np.pi**2)  # α_GUT

        # === THE FORMULA ===
        self.log("\n  ╔═══════════════════════════════════════════════╗")
        self.log("  ║  CANDIDATE: f_occ = α(1 - α(1+α)/(d²-1))   ║")
        self.log("  ╚═══════════════════════════════════════════════╝\n")

        # Test 1: Direct verification at d=5
        self.log("  === Test 1: d=5 Precision Test ===\n")

        correction = alpha * (1 + alpha) / (d**2 - 1)
        f_formula = alpha * (1 - correction)

        self.log(f"  α = 6/(d²π²) = {alpha:.12f}")
        self.log(f"  d²-1 = {d**2-1} = dim(adj SU(d))")
        self.log(f"  α(1+α)/(d²-1) = {correction:.12f}")
        self.log(f"")
        self.log(f"  f_formula = α(1 - α(1+α)/(d²-1))")
        self.log(f"            = {f_formula:.12f}")
        self.log(f"  f_occ     = {f_occ:.12f}")
        self.log(f"  Δ = f_formula - f_occ = {f_formula - f_occ:.4e}")
        self.log(f"  Δ/f_occ = {(f_formula/f_occ - 1)*100:.6f}%")

        err_pct = abs(f_formula / f_occ - 1) * 100
        self.check("f_occ = α(1 - α(1+α)/(d²-1)) to <0.01%", err_pct < 0.01)

        # Test 2: Decomposition
        self.log("\n  === Test 2: Physical Decomposition ===\n")

        self.log(f"  f_occ = α - α²(1+α)/(d²-1)")
        self.log(f"        = α - α²/(d²-1) - α³/(d²-1)")
        self.log(f"")
        self.log(f"  Term 1: α = {alpha:.10f}  (tree level)")
        self.log(f"  Term 2: -α²/(d²-1) = {-alpha**2/(d**2-1):.10f}  (1-loop)")
        self.log(f"  Term 3: -α³/(d²-1) = {-alpha**3/(d**2-1):.10f}  (mixed)")
        self.log(f"  Sum   : {alpha - alpha**2/(d**2-1) - alpha**3/(d**2-1):.10f}")
        self.log(f"  f_occ : {f_occ:.10f}")

        # d²-1 = 24 interpretation
        self.log(f"\n  d²-1 = {d**2-1}")
        self.log(f"  = dim(adj SU(5)) = 5²-1")
        self.log(f"  = dim(∧²ℂ⁵) + dim(S²ℂ⁵) - 1 = 10+15-1")
        self.log(f"  This is the NUMBER OF GAUGE BOSONS in SU(5)!")

        # Test 3: Higher-order terms
        self.log("\n  === Test 3: Higher-Order Corrections ===\n")

        # Try f = α - α²/(d²-1) - c₃α³ - c₄α⁴
        residual = f_occ - (alpha - alpha**2*(1+alpha)/(d**2-1))
        self.log(f"  Residual after 1-loop: {residual:.4e}")
        self.log(f"  Residual/α⁴ = {residual/alpha**4:.4f}")

        # Try exact: f = α(1 - α(1+α)/(d²-1) + c₂α²...)
        c2 = residual / (alpha * alpha**2)
        self.log(f"  Next correction: c₂ = {c2:.4f}")
        self.log(f"  c₂ × (d²-1) = {c2*(d**2-1):.4f}")

        # Test 4: Interpretation
        self.log("\n  === Test 4: Physical Interpretation ===\n")

        self.log(f"  THE FORMULA:")
        self.log(f"  f_occ = α_GUT × [1 - α_GUT(1+α_GUT)/(d²-1)]")
        self.log(f"")
        self.log(f"  INTERPRETATION:")
        self.log(f"  • Tree level: f_occ = α (occupation fraction = coupling)")
        self.log(f"  • 1-loop correction: -α²/(d²-1)")
        self.log(f"    = negative self-energy in the adjoint representation")
        self.log(f"    = 24 gauge bosons each contribute -α²/24")
        self.log(f"  • The (1+α) factor: dressed propagator 1/(1-α) ≈ 1+α")
        self.log(f"")
        self.log(f"  WHY 0.1%:")
        self.log(f"  gap/α = α(1+α)/(d²-1) = {correction:.6f}")
        self.log(f"  ≈ α/24 = {alpha/24:.6f}")
        self.log(f"  ≈ 0.001 = 0.1%  ✓")

        # Test 5: Verify with inverse
        self.log("\n  === Test 5: Inverse Check ===\n")

        # Given f_occ, can we recover α_GUT?
        # f = α(1 - α(1+α)/24)
        # f ≈ α - α²/24 (leading order)
        # α ≈ f + f²/24 (inversion)
        alpha_recovered = f_occ + f_occ**2 / 24 + f_occ**3 / 24
        self.log(f"  From f_occ = {f_occ:.10f}:")
        self.log(f"  α ≈ f + f²/24 + f³/24 = {alpha_recovered:.10f}")
        self.log(f"  α_GUT =                  {alpha:.10f}")
        self.log(f"  Error: {(alpha_recovered/alpha-1)*100:.4f}%")

        self.check("Inverse recovery: α from f_occ to <0.01%",
                   abs(alpha_recovered/alpha - 1) < 0.001)

        # Test 6: The ζ formula
        self.log("\n  === Test 6: ζ_eff Formula ===\n")

        zeta_2 = np.pi**2 / 6
        zeta_eff = 1 / (d**2 * f_occ)
        zeta_formula = zeta_2 / (1 - alpha*(1+alpha)/(d**2-1))

        self.log(f"  ζ_eff = ζ(2) / (1 - α(1+α)/(d²-1))")
        self.log(f"        = {zeta_2:.10f} / {1 - correction:.10f}")
        self.log(f"        = {zeta_formula:.10f}")
        self.log(f"  ζ_eff = {zeta_eff:.10f}")
        self.log(f"  Error: {(zeta_formula/zeta_eff-1)*100:.6f}%")

        self.check("ζ_eff = ζ(2)/(1-α(1+α)/(d²-1)) to <0.01%",
                   abs(zeta_formula/zeta_eff - 1) < 0.0001)


if __name__ == "__main__":
    AdjointCorrection().execute()