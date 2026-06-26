import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld
import E213.Lib.Math.NumberTheory.ModArith.CubicResidue

/-!
# The Eisenstein cubic symbol on a rational integer ⟺ rational cubic residue (Phase B0)

★★★★★ `cubic_symbol_rational_iff` : for the residue prime `d` (`‖d‖² = p ≡ 1 mod 3`) and a rational
unit `a` (`1 ≤ a < p`), the `ℤ[ω]` cubic symbol read on the embedded integer `↑a` is trivial **iff**
`a` is a cubic residue mod `p`:

  `(↑a / d)₃ = (↑a)^m ≡ 1 (mod d)  ⟺  ∃ y, y³ ≡ a (mod p)`.

This is the **bottom rung of Phase B** (the cubic reciprocity law): it pins the abstract `ℤ[ω]`
character `(·/d)₃` to the concrete rational cubic-residue predicate of `ModArith/CubicResidue`,
the foundation on which the supplementary laws and the reciprocity readout are stated.

## The chain

For `α = ofInt ↑a` the residue generator collapses (`α.re = ↑a`, `α.im = 0`), so no `x`-substitution
is needed — the symbol is the embedded rational power directly:

  `(↑a)^m ≡ 1 (mod d)`  ⟺[`ofInt_pow` + `p_dvd_of_dvd_ofInt`]  `p ∣ ((↑a)^m − 1)`
                        ⟺[`pow_mod_one_iff_int`, the ℕ↔ℤ bridge]  `a^m % p = 1`
                        ⟺[`pow_m_one_iff_cube`]  `a` is a cubic residue mod `p`.

The `⟸` half lifts via `ofInt_pow_modeq_one`; the `⟹` half descends the `ModEq` to a `d`-divisibility
and runs the norm transfer `p_dvd_of_dvd_ofInt`.  Carries `propext` (allowed-not-target per
`STRICT_ZERO_AXIOM.md`) **only** from Lean-core ℕ↔ℤ cast bookkeeping (`Int.natCast_pow`,
`Int.ofNat_sub`, `Nat.div_add_mod`); the number-theoretic core is PURE.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicSymbolRational

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_neg ofInt_add)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (ofInt_pow ofInt_pow_modeq_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld (p_dvd_of_dvd_ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.NumberTheory.ModArith.CubicResidue (pow_m_one_iff_cube)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat nat_dvd_to_int)

/-- **The ℕ↔ℤ power-residue bridge** — `p ∣ ((↑a)^m − 1)` in `ℤ` iff `a^m % p = 1` in `ℕ` (`1 ≤ a`,
    `1 < p`).  `⟹`: cast down through `natAbs`, write `a^m = p·k + 1`.  `⟸`: `a^m − 1 = p·(a^m/p)`
    (`Nat.div_add_mod`), cast up.  Carries `propext` from the core cast lemmas. -/
private theorem pow_mod_one_iff_int {a m p : Nat} (hp : 1 < p) (ha1 : 1 ≤ a) :
    (p : Int) ∣ ((a : Int) ^ m - 1) ↔ a ^ m % p = 1 := by
  have ham1 : 1 ≤ a ^ m := Nat.pos_pow_of_pos m (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1)
  have hcast : ((a ^ m : Nat) : Int) = (a : Int) ^ m := by rw [Int.natCast_pow]
  constructor
  · intro hint
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
  · intro hmod
    have hpnat : p ∣ (a ^ m - 1) := by
      have hdm : p * (a ^ m / p) + 1 = a ^ m := by
        have h := Nat.div_add_mod (a ^ m) p
        rwa [hmod] at h
      exact ⟨a ^ m / p, Nat.sub_eq_of_eq_add hdm.symm⟩
    have hsub : (((a ^ m - 1 : Nat)) : Int) = ((a : Int) ^ m - 1) := by
      rw [Int.ofNat_sub ham1, hcast]; rfl
    have h2 : (p : Int) ∣ (((a ^ m - 1 : Nat)) : Int) :=
      nat_dvd_to_int p (((a ^ m - 1 : Nat)) : Int) (by rwa [Int.natAbs_ofNat])
    rwa [hsub] at h2

/-- ★★★★★ **The Eisenstein cubic symbol on a rational integer ⟺ rational cubic residue.**  For the
    residue prime `d` (`‖d‖² = p`, `3m = p − 1`) and a rational unit `a` (`1 ≤ a < p`):

      `(↑a/d)₃ = (↑a)^m ≡ 1 (mod d)  ⟺  ∃ y, 1 ≤ y < p ∧ y³ ≡ a (mod p)`.

    The bottom rung of Phase B — the abstract `ℤ[ω]` symbol pinned to the rational cubic-residue
    predicate.  `⟹`: `ModEq` ⟶ `d ∣ ofInt((↑a)^m − 1)` ⟶[`p_dvd_of_dvd_ofInt`] `p ∣ ((↑a)^m − 1)`
    ⟶[`pow_mod_one_iff_int`] `a^m%p=1` ⟶[`pow_m_one_iff_cube`].  `⟸`: reverse, lifting via
    `ofInt_pow_modeq_one` (`d.normSq = ↑p`).  Carries `propext` only from ℕ↔ℤ cast bookkeeping. -/
theorem cubic_symbol_rational_iff {d : ZOmega} {a m p : Nat} (hp : 1 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (ha1 : 1 ≤ a) (halt : a < p) (hdp : d.normSq = (p : Int)) :
    ModEq d (pow (ofInt (a : Int)) m) (ofInt 1) ↔
      (∃ y : Nat, 1 ≤ y ∧ y < p ∧ y ^ 3 % p = a) := by
  have hbridge := pow_mod_one_iff_int (a := a) (m := m) (p := p) hp ha1
  constructor
  · intro hchar
    have hdvd : d ∣ ofInt ((a : Int) ^ m - 1) := by
      have hh : d ∣ (pow (ofInt (a : Int)) m + -ofInt 1) := hchar
      have e1 : pow (ofInt (a : Int)) m + -ofInt 1 = ofInt ((a : Int) ^ m - 1) := by
        rw [ofInt_pow, ← ofInt_neg, ofInt_add, Int.sub_eq_add_neg]
      rwa [e1] at hh
    have hpd : (p : Int) ∣ ((a : Int) ^ m - 1) := p_dvd_of_dvd_ofInt hp hpr hdp hdvd
    have hmod : a ^ m % p = 1 := hbridge.mp hpd
    exact (pow_m_one_iff_cube p m a hp hpr h3m hm1 ha1 halt).mp hmod
  · intro hcube
    have hmod : a ^ m % p = 1 := (pow_m_one_iff_cube p m a hp hpr h3m hm1 ha1 halt).mpr hcube
    have hpd : (p : Int) ∣ ((a : Int) ^ m - 1) := hbridge.mpr hmod
    have hdn : d.normSq ∣ ((a : Int) ^ m - 1) := by rw [hdp]; exact hpd
    exact ofInt_pow_modeq_one hdn

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicSymbolRational
