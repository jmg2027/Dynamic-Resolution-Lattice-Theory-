import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharWelldef
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle

/-!
# The `ℤ[ω]`-valued cubic character is multiplicative — `χ_ω(s)·χ_ω(t) = χ_ω(st)` (∅-axiom)

The keystone character identity.  For units `s, t ∈ 𝔽_p*`,

  `χ_ω(s) · χ_ω(t) = χ_ω((s·t) mod p)`.

`χ_ω` is `μ₃`-valued (`chiOmega_unit_value`).  The product `χ_ω(s)·χ_ω(t)` and `χ_ω(st)` are **congruent
mod `d`** — the lift `chiOmega_lift` plus the rational multiplicativity `cubicChar_mul` (a ring map
through `ℤ[ω]/(d) = 𝔽_p`) — and both lie in `μ₃`.  Since the three cube roots of unity are **distinct
mod `d`** (`EisensteinCubicCharWelldef.root_unique`, `p > 3`), congruence forces equality.

This is the multiplicativity a character must satisfy — the property that turns the Jacobi sum
manipulation (`Σ_t χ_ω(t) = 0` by scaling invariance) into the norm law `N(J) = p`.  The
supporting `μ₃` facts: `mu3_mul_closed` (closed under `·`), `mu3_inj` (injective mod `d`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq symm trans mul_right mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
  (chiOmega chiOmega_lift chiOmega_unit_value)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar cubicChar_mul cubicChar_mod)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots (ofInt_natMod_modEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (ofInt_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharWelldef (root_unique)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle (not_dvd_g)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)

/-- ★★★ **`μ₃` is closed under multiplication** — products of `{1, ω, ω²}` stay in `{1, ω, ω²}`
    (`ω³ = 1`).  The nine concrete cases by `decide`. -/
theorem mu3_mul_closed {u v : ZOmega}
    (hu : u = ofInt 1 ∨ u = Omega ∨ u = Omega * Omega)
    (hv : v = ofInt 1 ∨ v = Omega ∨ v = Omega * Omega) :
    u * v = ofInt 1 ∨ u * v = Omega ∨ u * v = Omega * Omega := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | (left; decide)
      | (right; left; decide)
      | (right; right; decide)

/-- ★★★ **`μ₃` injects into `ℤ[ω]/(d)`** — for `p > 3`, congruent cube roots of unity are equal
    (`root_unique`, restated with the `Omega·Omega` form of `ω²`). -/
theorem mu3_inj {d : ZOmega} {p : Nat} (hp3 : 3 < p) (hd : d.normSq = (p : Int))
    {u v : ZOmega}
    (hu : u = ofInt 1 ∨ u = Omega ∨ u = Omega * Omega)
    (hv : v = ofInt 1 ∨ v = Omega ∨ v = Omega * Omega)
    (h : ModEq d u v) : u = v := by
  have hΩ : Omega * Omega = Omega2 := by decide
  have conv : ∀ {w : ZOmega}, (w = ofInt 1 ∨ w = Omega ∨ w = Omega * Omega) →
      (w = ofInt 1 ∨ w = Omega ∨ w = Omega2) := by
    intro w hw
    rcases hw with h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (by rw [h0, hΩ]))
  exact root_unique hp3 hd (conv hu) (conv hv) h

/-- ★★★★★ **The cubic character `χ_ω` is multiplicative** — `χ_ω(s)·χ_ω(t) = χ_ω((s·t) mod p)` for
    units `s, t` (`0 < s, t < p`, `p > 3`).  Both sides are `μ₃`-valued and congruent mod `d` (the lift
    `chiOmega_lift` + the rational `cubicChar_mul`, a ring map through `𝔽_p`); `mu3_inj` (`root_unique`)
    upgrades congruence to equality.  The keystone toward the Jacobi-sum norm law.  ∅-axiom. -/
theorem chiOmega_mul {d : ZOmega} {p m x s t : Nat}
    (hp : 1 < p) (hp3 : 3 < p) (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p)
    (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hs1 : 0 < s) (hslt : s < p) (ht1 : 0 < t) (htlt : t < p) :
    chiOmega p m x s * chiOmega p m x t = chiOmega p m x ((s * t) % p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  -- `(s·t) mod p` is a unit
  have hnst : ¬ p ∣ (s * t) := fun hd =>
    (nat_prime_dvd_mul p hp hpr s t hd).elim (not_dvd_g s p hs1 hslt) (not_dvd_g t p ht1 htlt)
  have hstlt : (s * t) % p < p := Nat.mod_lt _ hppos
  have hstpos : 0 < (s * t) % p := by
    rcases Nat.eq_zero_or_pos ((s * t) % p) with h0 | hpos
    · exact absurd (dvd_of_mod_eq_zero h0) hnst
    · exact hpos
  -- the three lifts `ofInt ↑(cubicChar …) ≡ χ_ω …`
  have Ls := chiOmega_lift hp hpr h3m hdn hω hx hs1 hslt
  have Lt := chiOmega_lift hp hpr h3m hdn hω hx ht1 htlt
  have Lst := chiOmega_lift hp hpr h3m hdn hω hx hstpos hstlt
  -- `cubicChar((s·t) mod p) = (χ(s)·χ(t)) mod p`
  have hcst : cubicChar p m ((s * t) % p)
      = (cubicChar p m s * cubicChar p m t) % p := by
    rw [cubicChar_mod]; exact cubicChar_mul p m s t
  -- assemble the congruence `χ_ω(s)·χ_ω(t) ≡ χ_ω((s·t) mod p)`
  have C1 : ModEq d (chiOmega p m x s * chiOmega p m x t)
      (ofInt ((cubicChar p m s : Nat) : Int) * ofInt ((cubicChar p m t : Nat) : Int)) :=
    trans (mul_right (symm Ls) (chiOmega p m x t))
          (mul_left (symm Lt) (ofInt ((cubicChar p m s : Nat) : Int)))
  have E1 : ofInt ((cubicChar p m s : Nat) : Int) * ofInt ((cubicChar p m t : Nat) : Int)
      = ofInt (((cubicChar p m s * cubicChar p m t : Nat)) : Int) :=
    (ofInt_mul ((cubicChar p m s : Nat) : Int) ((cubicChar p m t : Nat) : Int)).symm
  have C2 : ModEq d (chiOmega p m x s * chiOmega p m x t)
      (ofInt (((cubicChar p m s * cubicChar p m t : Nat)) : Int)) := E1 ▸ C1
  have nm := ofInt_natMod_modEq (d := d) (p := p) (a := cubicChar p m s * cubicChar p m t) hdn
  have C3 : ModEq d (chiOmega p m x s * chiOmega p m x t)
      (ofInt ((((cubicChar p m s * cubicChar p m t) % p : Nat)) : Int)) := trans C2 (symm nm)
  have Lst' : ModEq d (ofInt ((((cubicChar p m s * cubicChar p m t) % p : Nat)) : Int))
      (chiOmega p m x ((s * t) % p)) := by
    rw [← hcst]; exact Lst
  have Ccong : ModEq d (chiOmega p m x s * chiOmega p m x t) (chiOmega p m x ((s * t) % p)) :=
    trans C3 Lst'
  -- both sides are `μ₃`-valued; `mu3_inj` finishes
  exact mu3_inj hp3 hdn
    (mu3_mul_closed (chiOmega_unit_value p m x s hs1 hslt) (chiOmega_unit_value p m x t ht1 htlt))
    (chiOmega_unit_value p m x ((s * t) % p) hstpos hstlt) Ccong

/-- ★★★ **The `μ₃` sum vanishes** — `1 + ω + ω² = 0`.  The algebraic kernel of cubic-character
    orthogonality: a full coset of cubic residues contributes `1 + ω + ω² = 0` to `Σ_t χ_ω(t)`, so the
    character sum over `𝔽_p*` is `0` (the missing combinatorial step is the equal-coset partition, i.e.
    the permutation-sum reindexing under `t ↦ a·t`).  ∅-axiom. -/
theorem mu3_sum_zero : ofInt 1 + Omega + Omega * Omega = 0 := by decide

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
