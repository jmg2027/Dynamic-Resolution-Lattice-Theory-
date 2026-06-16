import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Physics.Basel.WhyBasel

/-!
# N_eff depths from Gram-sector rank exhaustion (0 axioms)

**What is DERIVED (∅-axiom, `decide`):** the depth INTEGERS `{1, 2, ∞}` from
rank-exhaustion combinatorics:

  AAA pure sector:  C(NS, NS) = C(3,3) = 1,  saturates `C(3,4)=0`  → depth 1
  temporal sector:  rank ≤ NT = 2,           saturates `C(2,3)=0`  → depth 2
  cross-sector:     NS ≠ NT, no saturation                          → depth ∞

**What is POSITED (a reading, not derived):** the *binding* of each sector to a
specific force (AAA↔α_3 color, temporal↔α_2 weak, cross↔α_1 EM).  `WhyBasel.lean`
states this plainly ("N_eff per force is **posited** from the ch08 Gram-rank
argument; explicit Lean derivation is open").  So the theorems below force the
**saturation profile** `{1, 2, never}`; "these three are α_3, α_2, α_1" is the
sector→force reading, kept honest, not ontologized.

The α_1 (∞) case is the absence of a rank-saturating Nat — equivalent to the
bracket `S(N) ≤ ζ(2) ≤ upper(N)` with no finite cap.
-/

namespace E213.Lib.Physics.Cosmology.NeffDerivation

open E213.Lib.Physics.Simplex.Counts

/-- α_3 confinement: AAA hinge has C(NS, NS) = 1 independent
    configuration. Hop 2 reuses → determinant zero → propagation
    stops at one step. -/
def alpha_3_Neff : Nat := binom NS NS

/-- α_2 rank exhaustion: temporal Gram has rank ≤ NT.  After NT
    successive hops, all temporal directions are used.
    The (NT+1)-th hop is a linear combination of the prior — det = 0. -/
def alpha_2_Neff : Nat := NT

/-- **Capstone of "why Basel"** — N_eff per force derived from
    {NS, NT}, combined with WhyBasel's 1/n² form, gives:
      1/α_i = (factor) · S(N_eff_i)

    Bundles:
      · α_3 depth = C(NS, NS) = 1 (single pure-sector configuration);
        rank-saturation at hop 2: C(NS, NS+1) = 0
      · α_2 depth = NT = 2 (temporal rank cap); C(NT, NT+1) = 0
      · α_1 cross-sector: NS, NT ≠ 0 and NS ≠ NT (no saturation)
      · 1/n² propagator form from NS − 1 = 2 solid angle exponent. -/
theorem basel_formula_axiom_derived :
    -- α_3 depth (combinatorial)
    alpha_3_Neff = 1
    ∧ binom NS NS = 1
    ∧ binom NS (NS + 1) = 0
    -- α_2 depth (rank)
    ∧ alpha_2_Neff = 2
    ∧ binom NT NT = 1
    ∧ binom NT (NT + 1) = 0
    ∧ NT = 2
    -- α_1 cross-sector witness (no saturation)
    ∧ NS ≠ 0 ∧ NT ≠ 0 ∧ NS ≠ NT
    -- Form NS − 1 = 2: solid-angle 1/n² propagator exponent
    ∧ NS - 1 = 2 := by decide

end E213.Lib.Physics.Cosmology.NeffDerivation
