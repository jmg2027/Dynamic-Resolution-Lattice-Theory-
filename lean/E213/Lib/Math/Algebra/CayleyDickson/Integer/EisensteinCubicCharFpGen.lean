import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
import E213.Meta.Nat.MulMod213
import E213.Lib.Math.NumberTheory.FourSquareSeed

/-!
# `chiOmega` multiplicativity / non-vanishing for **any** unit (not just `< p`) (∅-axiom)

`chiOmega p m x` only sees its argument `mod p` (`chiOmega_mod`), so the multiplicativity `chiOmega_mul`
and non-vanishing `chiOmega_ne_zero` — originally stated for a reduced unit `0 < t < p` — hold for **any**
`t` coprime to `p` (`¬ p ∣ t`), via reduction to `t % p`.

This relaxation is what the cubic-reciprocity `π ↔ π'` transfer needs: the symmetric relation B uses the
second prime `π'` (norm `pr`) as the modulus with the *first* prime's norm `p` as the unit argument, where
`p > pr` is possible — so the `q < p` ordering constraint of the original split arc must be dropped to
`¬ p ∣ q` (which holds for distinct primes).  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpGen

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (Omega Omega2)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
  (chiOmega chiOmega_mod chiOmega_unit_value)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex (chiOmega_ne_zero)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Lib.Math.NumberTheory.FourSquareSeed (dvd_of_mod_zero)

/-- `0 < b % p` for `¬ p ∣ b` — the reduced residue of a unit is a positive residue. -/
private theorem mod_pos_of_not_dvd {p b : Nat} (hppos : 0 < p) (hb : ¬ p ∣ b) : 0 < b % p := by
  rcases Nat.eq_zero_or_pos (b % p) with h0 | h
  · exact absurd (dvd_of_mod_zero b p h0) hb
  · exact h

/-- ★★★ **`chiOmega` is non-zero on any unit** — `χ_ω(b) ≠ 0` for `¬ p ∣ b` (any size).  Reduce to
    `b % p` (`chiOmega_mod`), a positive residue `< p`, and apply `chiOmega_ne_zero`.  ∅-axiom. -/
theorem chiOmega_ne_zero_gen (p m x b : Nat) (hp : 1 < p) (hb : ¬ p ∣ b) :
    chiOmega p m x b ≠ 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  rw [← chiOmega_mod p m x b]
  exact chiOmega_ne_zero p m x (b % p) (mod_pos_of_not_dvd hppos hb) (Nat.mod_lt _ hppos)

/-- ★★★ **`chiOmega` multiplicativity on any units** — `χ_ω(s)·χ_ω(t) = χ_ω((s·t) mod p)` for `¬ p ∣ s`,
    `¬ p ∣ t` (any size).  Reduce `s, t` to `s % p, t % p` (`chiOmega_mod`), apply `chiOmega_mul`, and
    fold the residue product `(s%p · t%p)%p = (s·t)%p` (`mul_mod_pure`).  ∅-axiom. -/
theorem chiOmega_mul_gen {d : ZOmega} {p m x s t : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hs : ¬ p ∣ s) (ht : ¬ p ∣ t) :
    chiOmega p m x s * chiOmega p m x t = chiOmega p m x ((s * t) % p) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  rw [← chiOmega_mod p m x s, ← chiOmega_mod p m x t,
      chiOmega_mul hp hp3 hpr h3m hdn hω hx (mod_pos_of_not_dvd hppos hs) (Nat.mod_lt _ hppos)
        (mod_pos_of_not_dvd hppos ht) (Nat.mod_lt _ hppos),
      ← mul_mod_pure s t p]

/-- ★★★ **`chiOmega` is a literal `μ₃` element on any unit** — `χ_ω(b) ∈ {1, ω, ω²}` for `¬ p ∣ b`
    (any size).  Reduce to `b % p` (`chiOmega_mod`), a positive residue `< p`, and apply
    `chiOmega_unit_value` (rewriting its `ω·ω` branch to `ω²`).  ∅-axiom. -/
theorem chiOmega_unit_value_gen (p m x b : Nat) (hp : 1 < p) (hb : ¬ p ∣ b) :
    chiOmega p m x b = ofInt 1 ∨ chiOmega p m x b = Omega ∨ chiOmega p m x b = Omega2 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  rw [← chiOmega_mod p m x b]
  rcases chiOmega_unit_value p m x (b % p) (mod_pos_of_not_dvd hppos hb) (Nat.mod_lt _ hppos) with
    h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [h]; decide))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpGen
