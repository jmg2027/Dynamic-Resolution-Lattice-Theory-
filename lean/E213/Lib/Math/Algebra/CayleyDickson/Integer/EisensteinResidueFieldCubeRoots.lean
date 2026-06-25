import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue

/-!
# The residue-field cube roots of unity — `{1, ω, ω²} ≡ {1, x, x²} (mod d)` (∅-axiom, Phase A1)

The residue prime `d` (`‖d‖² = p ≡ 1 mod 3`) carries `ω ≡ x (mod d)` for a rational cube root `x`
(`p ∣ x²+x+1`, `EisensteinResiduePrime`).  Then the three cube roots of unity in `ℤ[ω]/(d)` reduce to
the three **rational** cube roots `{1, x, x²}` of `1` mod `p`:

  `1 ≡ 1`,  `ω ≡ x`,  `ω² ≡ x²`  (mod d).

This is the residue-field realisation of `μ₃` — the bridge needed to evaluate the cubic character on
**rational** residues `t ∈ 𝔽_p` (`χ(t) = the μ₃ value whose rational rep is `t^m mod p`), the first
brick of the Jacobi-sum core (`research-notes/frontiers/higher_reciprocity_roadmap.md`, Phase A1).
∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
  (ModEq refl trans mul_right mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (ofInt_mul)

/-- ★★★ **`ω² ≡ x² (mod d)`** from `ω ≡ x` — the squared cube root reduces to the squared rational
    root.  `ω·ω ≡ x·ω ≡ x·x` (`mul_right`/`mul_left`), then `ofInt_mul`. -/
theorem omega_sq_cong {d : ZOmega} {x : Int} (h : ModEq d Omega (ofInt x)) :
    ModEq d (Omega * Omega) (ofInt (x * x)) := by
  have h2 : ModEq d (Omega * Omega) (ofInt x * ofInt x) :=
    trans (mul_right h Omega) (mul_left h (ofInt x))
  rw [ofInt_mul]; exact h2

/-- ★★★★ **The residue-field cube roots of unity.**  Given `ω ≡ x (mod d)`, the three cube roots of
    unity `{1, ω, ω²}` of `ℤ[ω]/(d)` are congruent to the rational cube roots `{1, x, x²}` of `1` mod
    `p`:  `1 ≡ 1 ∧ ω ≡ x ∧ ω² ≡ x²`.  The residue-field realisation of `μ₃`.  ∅-axiom. -/
theorem cube_roots_rational {d : ZOmega} {x : Int} (h : ModEq d Omega (ofInt x)) :
    ModEq d (ofInt 1) (ofInt 1) ∧ ModEq d Omega (ofInt x) ∧
      ModEq d (Omega * Omega) (ofInt (x * x)) :=
  ⟨refl d (ofInt 1), h, omega_sq_cong h⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots
