import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Meta.Nat.AddMod213
import E213.Meta.Int213.PolyIntMTactic

/-!
# The residue-field cube roots of unity — `{1, ω, ω²} ≡ {1, x, x²} (mod d)` (∅-axiom)

The residue prime `d` (`‖d‖² = p ≡ 1 mod 3`) carries `ω ≡ x (mod d)` for a rational cube root `x`
(`p ∣ x²+x+1`, `EisensteinResiduePrime`).  Then the three cube roots of unity in `ℤ[ω]/(d)` reduce to
the three **rational** cube roots `{1, x, x²}` of `1` mod `p`:

  `1 ≡ 1`,  `ω ≡ x`,  `ω² ≡ x²`  (mod d).

This is the residue-field realisation of `μ₃` — the bridge needed to evaluate the cubic character on
**rational** residues `t ∈ 𝔽_p` (`χ(t) = the μ₃ value whose rational rep is `t^m mod p`), the first
brick of the Jacobi-sum core.
∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
  (ModEq refl symm trans mul_right mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (ofInt_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (modEq_ofInt_of_dvd)
open E213.Meta.Nat.AddMod213 (div_add_mod)

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

/-- ★★★ **Reduction mod `p` descends to mod `d`** — `ofInt ↑(a % p) ≡ ofInt ↑a (mod d)` when
    `‖d‖² = p`.  The rational reduction `a ↦ a % p` is invisible in `ℤ[ω]/(d)` (`p = ‖d‖²` is divisible
    by `d`), so a character value `t^m % p` and its un-reduced form agree mod `d`.  Via `↑a − ↑(a%p) =
    p·(a/p)` and `modEq_ofInt_of_dvd`.  ∅-axiom. -/
theorem ofInt_natMod_modEq {d : ZOmega} {p a : Nat} (hdn : d.normSq = (p : Int)) :
    ModEq d (ofInt ((a % p : Nat) : Int)) (ofInt ((a : Nat) : Int)) := by
  apply modEq_ofInt_of_dvd
  rw [hdn]
  have hc : ((a : Nat) : Int)
      = (p : Int) * ((a / p : Nat) : Int) + ((a % p : Nat) : Int) := by
    calc ((a : Nat) : Int)
        = (((p * (a / p) + a % p : Nat)) : Int) := by rw [div_add_mod a p]
      _ = (p : Int) * ((a / p : Nat) : Int) + ((a % p : Nat) : Int) := rfl
  refine ⟨-(((a / p : Nat) : Int)), ?_⟩
  rw [hc]; ring_intZ

/-- ★★★★ **A residue value `∈ {1, x, x²} mod p` lifts to `μ₃ ⊂ ℤ[ω]`.**  Given `ω ≡ x (mod d)`
    (`‖d‖² = p`) and a value `v` that is one of the three rational cube roots `{1, x % p, (x·x) % p}`
    (e.g. `v = χ(t) = t^m % p` via `CubicCharFp.cubicChar_trichotomy`), the lift `ofInt ↑v` is congruent
    mod `d` to one of `{1, ω, ω²}`.  The bridge that makes the cubic character genuinely `μ₃`-valued in
    `ℤ[ω]`.  `ofInt_natMod_modEq` strips the `% p`, then `cube_roots_rational` / `omega_sq_cong`.
    ∅-axiom. -/
theorem natMod_value_omega_power {d : ZOmega} {p x v : Nat} (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hv : v = 1 ∨ v = x % p ∨ v = (x * x) % p) :
    ModEq d (ofInt ((v : Nat) : Int)) (ofInt 1) ∨
      ModEq d (ofInt ((v : Nat) : Int)) Omega ∨
      ModEq d (ofInt ((v : Nat) : Int)) (Omega * Omega) := by
  rcases hv with h1 | hx | hxx
  · left; rw [h1]; exact refl d (ofInt 1)
  · right; left; rw [hx]
    exact trans (ofInt_natMod_modEq hdn) (symm hω)
  · right; right; rw [hxx]
    exact trans (ofInt_natMod_modEq hdn) (symm (omega_sq_cong hω))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots
