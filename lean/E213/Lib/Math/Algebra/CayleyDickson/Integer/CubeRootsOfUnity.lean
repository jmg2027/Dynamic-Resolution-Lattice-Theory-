import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaUnits
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd

/-!
# The cube roots of unity in `ℤ[ω]` — the value group `μ₃` (∅-axiom)

★★★★ `cube_root_unity` : `x³ = 1 ⟺ x ∈ {1, ω, ω²}` in `ℤ[ω]`.

The three cube roots of unity `μ₃ = {1, ω, ω²}` are the **value group of the cubic-residue character**
`(·/π)₃` (the Eisenstein analogue of the Legendre symbol's `{±1}`): the character of a unit `α` mod a
prime `π` of norm `p ≡ 1 (mod 3)` is the unique `ζ ∈ μ₃` with `α^{(p−1)/3} ≡ ζ (mod π)`.  This file
pins down the codomain — the first rung toward cubic (Eisenstein) reciprocity.

Proof: `x³ = 1` makes `x` a unit (inverse `x²`), so `‖x‖² = 1` (`normSq_one_of_unit`), hence `x` is one
of the six Eisenstein units (`normSq_one_in_units6`); among those exactly three cube to `1` (the other
three cube to `−1`), extracted purely from the `BEq` membership chain (`of_decide_eq_true` per branch,
no `propext`-tainted `List` lemmas).  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.CubeRootsOfUnity

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd (normSq_one_of_unit)

/-- `(a || b) = true → a = true ∨ b = true` (∅-axiom; inlined to avoid a cross-tree import). -/
private theorem orB_elim {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

/-- ★★★★ **The cube roots of unity in `ℤ[ω]` are exactly `{1, ω, ω²}`.**  `x³ = 1 ⟺ x = 1 ∨ x = ω ∨
    x = ω²` — the value group `μ₃` of the cubic-residue character.  `⟹`: `x³ = 1` ⟹ `x` is a unit
    (norm 1) ⟹ one of the six units, of which exactly the three listed cube to `1`.  `⟸`: each cubes
    to `1` by computation.  ∅-axiom. -/
theorem cube_root_unity (x : ZOmega) :
    x * x * x = ofInt 1 ↔ (x = ofInt 1 ∨ x = Omega ∨ x = Omega2) := by
  constructor
  · intro h
    have hx : x * (x * x) = ofInt 1 := by rw [← mul_comm (x * x) x]; exact h
    have hn : x.normSq = 1 := normSq_one_of_unit x (x * x) hx
    have hc : units6.contains x = true := normSq_one_in_units6 x hn
    rcases orB_elim hc with h1 | hc
    · have hx1 : x = ⟨1, 0⟩ := of_decide_eq_true h1; subst hx1; exact Or.inl rfl
    · rcases orB_elim hc with h2 | hc
      · have hx2 : x = ⟨-1, 0⟩ := of_decide_eq_true h2; subst hx2; exact absurd h (by decide)
      · rcases orB_elim hc with h3 | hc
        · have hx3 : x = ⟨0, 1⟩ := of_decide_eq_true h3; subst hx3; exact Or.inr (Or.inl rfl)
        · rcases orB_elim hc with h4 | hc
          · have hx4 : x = ⟨0, -1⟩ := of_decide_eq_true h4; subst hx4; exact absurd h (by decide)
          · rcases orB_elim hc with h5 | hc
            · have hx5 : x = ⟨1, 1⟩ := of_decide_eq_true h5; subst hx5; exact absurd h (by decide)
            · rcases orB_elim hc with h6 | hf
              · have hx6 : x = ⟨-1, -1⟩ := of_decide_eq_true h6; subst hx6; exact Or.inr (Or.inr rfl)
              · exact Bool.noConfusion hf
  · rintro (rfl | rfl | rfl) <;> decide

/-- `ω` is a primitive cube root: `ω ≠ 1` but `ω³ = 1`. -/
theorem omega_primitive : Omega ≠ ofInt 1 ∧ Omega * Omega * Omega = ofInt 1 := by decide

/-- `ω²` is the other primitive cube root, and `ω · ω² = 1` (the group law on `μ₃`). -/
theorem omega2_facts :
    Omega2 = Omega * Omega ∧ Omega * Omega2 = ofInt 1 ∧ Omega2 * Omega2 * Omega2 = ofInt 1 := by
  decide

end E213.Lib.Math.Algebra.CayleyDickson.Integer.CubeRootsOfUnity
