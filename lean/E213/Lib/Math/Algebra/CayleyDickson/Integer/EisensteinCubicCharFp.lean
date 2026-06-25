import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots
import E213.Lib.Math.NumberTheory.ModArith.CubicCharFp

/-!
# The `ℤ[ω]`-valued cubic character on `𝔽_p` — `χ_ω : ℕ → ℤ[ω]` (∅-axiom, Phase A1/A2)

The cubic character valued in `μ₃ ⊂ ℤ[ω]` (rather than as a rational residue) — the form the Jacobi sum
needs.  Given the residue prime `d` (`‖d‖² = p`, `ω ≡ x mod d`) and the cube root `x` (`p ∣ x²+x+1`),

  `χ_ω(t) := 0` if `p ∣ t`,  else the `ω`-power matching `t^m % p ∈ {1, x, x²}`:
  `ofInt 1` / `Omega` / `Omega·Omega`.

This is a **computable** function (`Nat` decidable equality picks the branch).  Its defining property is
the **lift congruence** `ofInt ↑(χ(t)) ≡ χ_ω(t) (mod d)` for a unit `t` (`chiOmega_lift`): the rational
character value `t^m % p` and the `μ₃`-element `χ_ω(t)` agree in the residue field `ℤ[ω]/(d) = 𝔽_p`.  So
`χ_ω` *is* the cubic character, now taking genuine cube-root-of-unity values in `ℤ[ω]`.

The selector relies on the value trichotomy `CubicCharFp.cubicChar_trichotomy` and the branch lifts of
`EisensteinResidueFieldCubeRoots` (`ofInt_natMod_modEq`, `cube_roots_rational`, `omega_sq_cong`).
∅-axiom.  (Multiplicativity `χ_ω(st) = χ_ω(s)χ_ω(t)`, needing residue-field injectivity
`root_unique` for `p > 3`, is deferred — `research-notes/frontiers/higher_reciprocity_roadmap.md` A1.)
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq refl symm trans)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots
  (omega_sq_cong ofInt_natMod_modEq)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar cubicChar_trichotomy)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)

/-- The `ℤ[ω]`-valued cubic character: `χ_ω(t) = 0` if `p ∣ t`, else the `μ₃`-element whose rational
    representative is `t^m % p ∈ {1, x, x²}`. -/
def chiOmega (p m x t : Nat) : ZOmega :=
  if t % p = 0 then 0
  else if cubicChar p m t = 1 then ofInt 1
  else if cubicChar p m t = x % p then Omega
  else Omega * Omega

/-- ★★★ **`χ_ω` is `{0, 1, ω, ω²}`-valued.**  By construction the four `if`-branches. -/
theorem chiOmega_value (p m x t : Nat) :
    chiOmega p m x t = 0 ∨ chiOmega p m x t = ofInt 1 ∨
      chiOmega p m x t = Omega ∨ chiOmega p m x t = Omega * Omega := by
  unfold chiOmega
  by_cases h0 : t % p = 0
  · rw [if_pos h0]; exact Or.inl rfl
  · rw [if_neg h0]
    by_cases h1 : cubicChar p m t = 1
    · rw [if_pos h1]; exact Or.inr (Or.inl rfl)
    · rw [if_neg h1]
      by_cases h2 : cubicChar p m t = x % p
      · rw [if_pos h2]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [if_neg h2]; exact Or.inr (Or.inr (Or.inr rfl))

/-- ★★★★ **The lift congruence** — `ofInt ↑(χ(t)) ≡ χ_ω(t) (mod d)` for a unit `t` (`0 < t < p`).  The
    rational character value `t^m % p` and the `μ₃`-element `χ_ω(t)` are congruent in `ℤ[ω]/(d) = 𝔽_p`,
    i.e. `χ_ω` represents the cubic character with genuine cube-root-of-unity values.  The trichotomy
    selects the branch; `ofInt_natMod_modEq` + `cube_roots_rational` / `omega_sq_cong` lift it.
    ∅-axiom. -/
theorem chiOmega_lift {d : ZOmega} {p m x t : Nat} (hp : 1 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ht1 : 0 < t) (htlt : t < p) :
    ModEq d (ofInt ((cubicChar p m t : Nat) : Int)) (chiOmega p m x t) := by
  have htnz : ¬ t % p = 0 := by rw [Nat.mod_eq_of_lt htlt]; exact Nat.ne_of_gt ht1
  unfold chiOmega
  rw [if_neg htnz]
  by_cases h1 : cubicChar p m t = 1
  · rw [if_pos h1, h1]; exact refl d (ofInt ((1 : Nat) : Int))
  · rw [if_neg h1]
    by_cases h2 : cubicChar p m t = x % p
    · rw [if_pos h2, h2]; exact trans (ofInt_natMod_modEq hdn) (symm hω)
    · rw [if_neg h2]
      rcases cubicChar_trichotomy p m x t hp hpr h3m hx ht1 htlt with e1 | e2 | e3
      · exact absurd e1 h1
      · exact absurd e2 h2
      · rw [e3]; exact trans (ofInt_natMod_modEq hdn) (symm (omega_sq_cong hω))

/-- ★★★★ **Character values are units of norm 1** — `χ_ω(t) · conj χ_ω(t) = 1` whenever `χ_ω(t) ≠ 0`.
    Each nonzero value is in `{1, ω, ω²}`, all of norm `1` (`mul_conj_self` gives `ofInt ‖·‖²` and the
    three norms are `1`).  The `|χ(t)| = 1` metric behind `|J(χ,χ)|² = p`.  ∅-axiom. -/
theorem chiOmega_mul_conj (p m x t : Nat) (h : chiOmega p m x t ≠ 0) :
    chiOmega p m x t * (chiOmega p m x t).conj = ofInt 1 := by
  rcases chiOmega_value p m x t with h0 | h1 | hw | hw2
  · exact absurd h0 h
  · rw [h1, mul_conj_self, show (ofInt 1).normSq = 1 from by decide]
  · rw [hw, mul_conj_self, show Omega.normSq = 1 from by decide]
  · rw [hw2, mul_conj_self, show (Omega * Omega).normSq = 1 from by decide]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
