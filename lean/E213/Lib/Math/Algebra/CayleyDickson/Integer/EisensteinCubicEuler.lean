import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld
import E213.Lib.Math.NumberTheory.ModArith.CubicResidue
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Meta.Int213.PolyIntMTactic

/-!
# The cubic Euler criterion for `ℤ[ω]` — `(α/d)₃ = 1 ⟹ α is a cube mod d`

★★★★★ `char_one_implies_cube` : for the residue prime `d` (`‖d‖² = p ≡ 1 mod 3`) and `α ≡ ↑r (mod d)`
whose rational reduction `r` has a Nat residue `a ≡ r (mod p)`, a **trivial cubic character** forces
`α` to be a **cube** in `ℤ[ω]/(d)`:

  `(α/d)₃ = α^m ≡ 1 (mod d)  ⟹  ∃ y : ℤ,  α ≡ (↑y)³ (mod d)`.

The hard (converse) direction of the cubic Euler criterion for the Eisenstein character — companion to
`EisensteinCubicChar.cubic_residue_char_one` (the easy `cube ⟹ χ = 1`).  Assembly of the
previously-built PURE pieces:

  `(α/d)₃ = 1`  →[`rational_of_char_one`]  `p ∣ (r^m − 1)`
              →[`int_dvd_pow_sub_pow` + `r ≡ a`]  `p ∣ (a^m − 1)`,  i.e. `a^m ≡ 1 (mod p)`
              →[`pow_m_one_iff_cube`]  `∃ x, x³ ≡ a (mod p)`  (rational cubic residue)
              →[`cube_lift`]  `α ≡ (↑x)³ (mod d)`.

Carries `propext` (allowed-not-target per `STRICT_ZERO_AXIOM.md`) **only** from Lean-core ℕ↔ℤ cast
bookkeeping (`Int.natCast_pow`, `Int.ofNat_sub`, `Int.natCast_mul`); the number-theoretic core
(`int_dvd_pow_sub_pow`, the weld, `cube_lift`, `pow_m_one_iff_cube`) is PURE.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicEuler

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (cube_lift)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld (rational_of_char_one)
open E213.Lib.Math.NumberTheory.ModArith.CubicResidue (pow_m_one_iff_cube)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)

/-- ★★★ **Power congruence (∅-axiom).**  `n ∣ (a − b) ⟹ n ∣ (aᵏ − bᵏ)` in `ℤ`, by induction:
    `a^{k+1} − b^{k+1} = a·(aᵏ − bᵏ) + bᵏ·(a − b)`.  PURE. -/
theorem int_dvd_pow_sub_pow {n a b : Int} (h : n ∣ (a - b)) :
    ∀ k : Nat, n ∣ (a ^ k - b ^ k)
  | 0 => ⟨0, by rw [Int.pow_zero, Int.pow_zero, Int.mul_zero]; decide⟩
  | k + 1 => by
      obtain ⟨c1, hc1⟩ := int_dvd_pow_sub_pow h k
      obtain ⟨c2, hc2⟩ := h
      refine ⟨a * c1 + b ^ k * c2, ?_⟩
      have key : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by
        rw [Int.pow_succ, Int.pow_succ]; ring_intZ
      rw [key, hc1, hc2]; ring_intZ

/-- `a^m % p = 1` from `p ∣ ((↑a)^m − 1)` in `ℤ` (`1 ≤ a`, `1 < p`).  ℕ↔ℤ cast bridge. -/
private theorem nat_pow_mod_one {a m p : Nat} (hp : 1 < p) (ha1 : 1 ≤ a)
    (hint : (p : Int) ∣ ((a : Int) ^ m - 1)) : a ^ m % p = 1 := by
  have ham1 : 1 ≤ a ^ m := Nat.pos_pow_of_pos m (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1)
  have hcast : ((a ^ m : Nat) : Int) = (a : Int) ^ m := by rw [Int.natCast_pow]
  have hdInt : (p : Int) ∣ (((a ^ m : Nat) : Int) - 1) := by rw [hcast]; exact hint
  have hsub : (((a ^ m : Nat) : Int) - 1) = (((a ^ m - 1 : Nat)) : Int) := by
    rw [Int.ofNat_sub ham1]; rfl
  rw [hsub] at hdInt
  have hpnat : p ∣ (a ^ m - 1) := by
    have h2 := int_dvd_to_nat p (((a ^ m - 1 : Nat)) : Int) hdInt
    rwa [Int.natAbs_ofNat] at h2
  obtain ⟨k, hk⟩ := hpnat
  have heq : a ^ m = p * k + 1 := by rw [← Nat.sub_add_cancel ham1, hk]
  rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

/-- ★★★★★ **Cubic Euler criterion for `ℤ[ω]` (converse direction).**  For the residue prime `d`
    (`‖d‖² = p`) and `α ≡ ↑r (mod d)` with a Nat residue `a` of `r` (`1 ≤ a < p`, `r ≡ a mod p`),
    `(α/d)₃ = α^m ≡ 1 (mod d)` forces `α ≡ (↑x)³ (mod d)` for some `x : ℤ` — `α` is a cube mod `d`.
    Carries `propext` only from ℕ↔ℤ cast bookkeeping. -/
theorem char_one_implies_cube {d α : ZOmega} {x : Int} {r : Int} {a m p : Nat}
    (hp : 1 < p) (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (ha1 : 1 ≤ a) (halt : a < p) (hdp : d.normSq = (p : Int))
    (hxr : r = α.re + α.im * x) (hred : ModEq d α (ofInt r))
    (hcong : (p : Int) ∣ (r - (a : Int)))
    (hchar : ModEq d (pow α m) (ofInt 1)) :
    ∃ y : Int, ModEq d α (ofInt y * ofInt y * ofInt y) := by
  -- weld: p ∣ (r^m − 1)
  have hweld : (p : Int) ∣ (r ^ m - 1) := by
    have hredx : ModEq d α (ofInt (α.re + α.im * x)) := hxr ▸ hred
    have h := rational_of_char_one hp hpr hdp hredx hchar
    rwa [← hxr] at h
  -- r ≡ a  ⟹  p ∣ (r^m − a^m), then subtract to get p ∣ (a^m − 1)
  have hpow : (p : Int) ∣ (r ^ m - (a : Int) ^ m) := int_dvd_pow_sub_pow hcong m
  have hint : (p : Int) ∣ ((a : Int) ^ m - 1) := by
    obtain ⟨u, hu⟩ := hweld; obtain ⟨v, hv⟩ := hpow
    refine ⟨u - v, ?_⟩
    have e : (a : Int) ^ m - 1 = (r ^ m - 1) - (r ^ m - (a : Int) ^ m) := by ring_intZ
    rw [e, hu, hv]; ring_intZ
  -- ℕ side, rational cubic residue
  have hnat : a ^ m % p = 1 := nat_pow_mod_one hp ha1 hint
  obtain ⟨xn, hxn1, hxnlt, hxn3⟩ := (pow_m_one_iff_cube p m a hp hpr h3m hm1 ha1 halt).mp hnat
  -- `xn³ = xn·xn·xn`, so `p ∣ (xn·xn·xn − a)`
  have h3eq : xn ^ 3 = xn * xn * xn := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
        Nat.pow_succ, show (1 : Nat) = 0 + 1 from rfl, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [h3eq] at hxn3
  have haxn : a ≤ xn * xn * xn := by rw [← hxn3]; exact Nat.mod_le _ _
  have hxn_dvd : p ∣ (xn * xn * xn - a) := by
    have hdm : p * (xn * xn * xn / p) + a = xn * xn * xn := by
      have h := Nat.div_add_mod (xn * xn * xn) p
      rwa [hxn3] at h
    exact ⟨xn * xn * xn / p, Nat.sub_eq_of_eq_add hdm.symm⟩
  -- cast to ℤ and combine with `r ≡ a`
  have hxn_int : (p : Int) ∣ ((xn : Int) * (xn : Int) * (xn : Int) - (a : Int)) := by
    obtain ⟨cc, hcc⟩ := hxn_dvd
    refine ⟨(cc : Int), ?_⟩
    have ecast : ((xn : Int) * (xn : Int) * (xn : Int) - (a : Int))
        = (((xn * xn * xn - a : Nat)) : Int) := by
      rw [Int.ofNat_sub haxn, Int.natCast_mul, Int.natCast_mul]
    rw [ecast, hcc, Int.natCast_mul]
  have hfin : (p : Int) ∣ ((xn : Int) * (xn : Int) * (xn : Int) - r) := by
    obtain ⟨s, hs⟩ := hxn_int; obtain ⟨t, ht⟩ := hcong
    refine ⟨s - t, ?_⟩
    have e : (xn : Int) * (xn : Int) * (xn : Int) - r
        = ((xn : Int) * (xn : Int) * (xn : Int) - (a : Int)) - (r - (a : Int)) := by ring_intZ
    rw [e, hs, ht]; ring_intZ
  exact ⟨(xn : Int), cube_lift hred (by rw [hdp]; exact hfin)⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicEuler
