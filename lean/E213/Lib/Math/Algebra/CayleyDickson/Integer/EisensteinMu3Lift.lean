import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative

/-!
# The μ₃ lift — a `mod q` congruence between cube roots of unity **is** equality (∅-axiom)

★★★★★ `mu3_eq_of_modEq` : for a rational prime `q > 1` (in fact any `q > 1`), if two μ₃ values
`X, Y ∈ {1, ω, ω²}` are congruent modulo `q` in `ℤ[ω]`,

  `X ≡ Y   (mod q)   ⟹   X = Y`.

The residue character `J^{(q²−1)/3} ≡ χ(q) (mod q)` (`cubic_reciprocity_power_congr`) is a congruence
of μ₃ values; this lemma upgrades it to the **equality** `(π/q)₃ = χ(q)` the reciprocity law needs.

Proof: each of the six ordered distinct pairs `X − Y` has a coordinate (`.re` or `.im`) equal to `±1`
— `ω−1 = ⟨−1,1⟩`, `ω²−1 = ⟨−2,−1⟩`, `ω²−ω = ⟨−1,−2⟩` and their negatives.  `q ∣ (X−Y)` forces
`q ∣ (±1)` on that coordinate (`dvd_re_of_ofInt_dvd` / `dvd_im_of_ofInt_dvd`), reflected to `q ∣ 1` over
`ℕ` (`int_dvd_to_nat`, since `(±1).natAbs = 1`), hence `q = 1` (`eq_one_of_dvd_one`), contradicting
`q > 1`.  No coordinate of a μ₃ difference is a multiple of any `q > 1`, so distinct μ₃ values stay
distinct mod every such `q`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega Omega2)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat
  (dvd_re_of_ofInt_dvd dvd_im_of_ofInt_dvd)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (eq_one_of_dvd_one)

/-- **A unit coordinate is divisible by no `q > 1`.**  If `c.natAbs = 1` then `↑q ∤ c` for `q > 1`:
    `int_dvd_to_nat` reflects `↑q ∣ c` to `q ∣ c.natAbs = 1`, so `q = 1` — absurd.  ∅-axiom. -/
private theorem unit_not_dvd {q : Nat} (hq : 1 < q) {c : Int} (hc : c.natAbs = 1) :
    ¬ ((q : Int) ∣ c) := fun hdvd => by
  have hd : q ∣ c.natAbs := int_dvd_to_nat q c hdvd
  rw [hc] at hd
  have hq1 : q = 1 := eq_one_of_dvd_one hd
  rw [hq1] at hq
  exact absurd hq (by decide)

/-- ★★★★★ **The μ₃ lift** — a `mod q` congruence between cube roots of unity is an equality, for any
    `q > 1`.  Each distinct ordered pair leaves a `±1` coordinate in `X − Y`; `q ∣ (X−Y)` would force
    `q ∣ (±1)`, impossible for `q > 1`.  Upgrades `J^{(q²−1)/3} ≡ χ(q)` to `(π/q)₃ = χ(q)`.
    ∅-axiom (PURE). -/
theorem mu3_eq_of_modEq {q : Nat} (hq : 1 < q) {X Y : ZOmega}
    (hX : X = ofInt 1 ∨ X = Omega ∨ X = Omega2)
    (hY : Y = ofInt 1 ∨ Y = Omega ∨ Y = Omega2)
    (h : ModEq (ofInt ((q : Nat) : Int)) X Y) : X = Y := by
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd (dvd_re_of_ofInt_dvd h) (unit_not_dvd hq (by decide))
      | exact absurd (dvd_im_of_ofInt_dvd h) (unit_not_dvd hq (by decide))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift
