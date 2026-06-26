import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinIntFermat
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Meta.Tactic.Pow213

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
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd (normSq_dvd_of_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)

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

/-- **A μ₃ difference has norm `3`, divisible by no prime `> 3`.**  If `diff.normSq = 3` and `π' ∣ diff`
    with `‖π'‖² = pr > 3`, then `pr ∣ 3` (norm respects divisibility), so `pr ≤ 3` — absurd.  ∅-axiom. -/
private theorem norm3_absurd {pr : Nat} {π' diff : ZOmega} (hpr3 : 3 < pr)
    (hπ'norm : π'.normSq = (pr : Int)) (hn : diff.normSq = 3) (hd : π' ∣ diff) : False := by
  obtain ⟨c, hc⟩ := hd
  have hnd : π'.normSq ∣ diff.normSq := normSq_dvd_of_dvd π' diff c hc
  rw [hπ'norm, hn] at hnd
  have hnat : pr ∣ (3 : Nat) := by
    have h := int_dvd_to_nat pr 3 hnd
    rwa [show (3 : Int).natAbs = 3 from rfl] at h
  exact absurd (le_of_dvd_pos pr 3 (by decide) hnat) (Nat.not_le.mpr hpr3)

/-- ★★★★★ **The μ₃ lift, Eisenstein-prime modulus** — a `mod π'` congruence between cube roots of unity
    is an equality, for an Eisenstein prime `π'` of prime norm `pr > 3`.  Each distinct μ₃ difference has
    norm `3` (`‖ω−1‖² = ‖ω²−1‖² = ‖ω²−ω‖² = 3`); `π' ∣ (X−Y)` forces `pr ∣ 3` — impossible for `pr > 3`.
    The Eisenstein-modulus analog of `mu3_eq_of_modEq` (rational modulus) needed to pin the cross-modulus
    cubic residue symbols `(π/π')₃`, `(π'/π)₃` to literal cube roots of unity.  ∅-axiom (PURE). -/
theorem mu3_eq_of_modEq_pi {pr : Nat} {π' : ZOmega} (hpr3 : 3 < pr)
    (hπ'norm : π'.normSq = (pr : Int)) {X Y : ZOmega}
    (hX : X = ofInt 1 ∨ X = Omega ∨ X = Omega2)
    (hY : Y = ofInt 1 ∨ Y = Omega ∨ Y = Omega2)
    (h : ModEq π' X Y) : X = Y := by
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    first
      | rfl
      | exact (norm3_absurd hpr3 hπ'norm (by decide) h).elim

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift
