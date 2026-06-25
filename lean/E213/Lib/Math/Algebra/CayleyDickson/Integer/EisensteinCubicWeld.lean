import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Meta.Int213.PolyIntMTactic

/-!
# The cubic character ⟺ rational power-residue, both directions (∅-axiom)

★★★★★ `char_one_iff_rational` : for the residue prime `d` (`‖d‖² = p`) and `α ≡ ↑r (mod d)` with
`r = α.re + α.im·x`,

  `(α/d)₃ = 1  ⟺  p ∣ (r^m − 1)`,

i.e. the Eisenstein cubic character is trivial **iff** the rational power-residue `r^m ≡ 1 (mod p)`.
This closes the weld leg left open in `EisensteinCubicChar`: the `⟸` direction (`char_one_of_rational`)
was already there; the `⟹` direction needs the **`d → p` transfer** `d ∣ ↑k ⟹ p ∣ k` proved here from
the norm (`‖d‖² = p` prime) and the rational Euclid lemma `nat_prime_dvd_mul`.

Together with `ModArith/CubicResidue.cube_iff_three_dvd_dlog` (`r^m ≡ 1 ⟺ r` cubic residue `⟺ 3 ∣
dlog_g(r)`), this makes `(·/d)₃` a fully computable `μ₃`-valued cubic-residue symbol on `ℤ[ω]`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq trans symm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd (normSq_dvd_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_neg ofInt_add)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
  (char_eq_rational_pow char_one_of_rational)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat nat_dvd_to_int)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)

/-- `(k·k).natAbs = k.natAbs · k.natAbs` — the pure (`rfl`-by-cases) square case of `Int.natAbs_mul`
    (which is `propext`-dirty in core). -/
private theorem natAbs_mul_self (k : Int) : (k * k).natAbs = k.natAbs * k.natAbs := by
  cases k with
  | ofNat n => rfl
  | negSucc n => rfl

/-- ★★★★ **The `d → p` transfer** — for a norm-`p` (prime) `d`, `d ∣ ↑k` in `ℤ[ω]` forces `p ∣ k` in
    `ℤ`.  Take norms: `p = ‖d‖² ∣ ‖↑k‖² = k²`, so `p ∣ k²`; by the rational Euclid lemma
    (`nat_prime_dvd_mul`, lifted through `natAbs`), `p ∣ k`.  The converse of `modEq_ofInt_of_dvd`.
    ∅-axiom. -/
theorem p_dvd_of_dvd_ofInt {d : ZOmega} {p : Nat} (hp : 1 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hdp : d.normSq = (p : Int)) {k : Int}
    (h : d ∣ ofInt k) : (p : Int) ∣ k := by
  obtain ⟨c, hc⟩ := h
  have hnorm : d.normSq ∣ (ofInt k).normSq := normSq_dvd_of_dvd d (ofInt k) c hc
  have hk2 : (ofInt k).normSq = k * k := by
    show k * k - k * 0 + 0 * 0 = k * k
    rw [Int.mul_zero, Int.mul_zero, Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero, Int.add_zero]
  rw [hk2, hdp] at hnorm
  have hnat : p ∣ k.natAbs * k.natAbs := by
    have hh := int_dvd_to_nat p (k * k) hnorm
    rwa [natAbs_mul_self] at hh
  rcases nat_prime_dvd_mul p hp hpr k.natAbs k.natAbs hnat with h1 | h1 <;>
    exact nat_dvd_to_int p k h1

/-- ★★★★ **Trivial Eisenstein character ⟹ rational cubic residue** — if `(α/d)₃ = α^m ≡ 1 (mod d)`,
    then `p ∣ r^m − 1` (`r^m ≡ 1 mod p`, `r = α.re + α.im·x`).  From `char_eq_rational_pow`,
    `↑(r^m) ≡ ↑1 (mod d)`, i.e. `d ∣ ↑(r^m − 1)`; the `d → p` transfer gives `p ∣ (r^m − 1)`.
    ∅-axiom. -/
theorem rational_of_char_one {d α : ZOmega} {x : Int} {m : Nat} {p : Nat} (hp : 1 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hdp : d.normSq = (p : Int))
    (hred : ModEq d α (ofInt (α.re + α.im * x)))
    (hchar : ModEq d (pow α m) (ofInt 1)) :
    (p : Int) ∣ ((α.re + α.im * x) ^ m - 1) := by
  have hrm : ModEq d (ofInt ((α.re + α.im * x) ^ m)) (ofInt 1) :=
    trans (symm (char_eq_rational_pow hred)) hchar
  have hdvd : d ∣ ofInt ((α.re + α.im * x) ^ m - 1) := by
    have e1 : ofInt ((α.re + α.im * x) ^ m) + -ofInt 1 = ofInt ((α.re + α.im * x) ^ m - 1) := by
      rw [← ofInt_neg, ofInt_add, Int.sub_eq_add_neg]
    have hh : d ∣ (ofInt ((α.re + α.im * x) ^ m) + -ofInt 1) := hrm
    rwa [e1] at hh
  exact p_dvd_of_dvd_ofInt hp hpr hdp hdvd

/-- ★★★★★ **The cubic character is the rational power-residue** — `(α/d)₃ = 1 ⟺ p ∣ (r^m − 1)`
    (`r = α.re + α.im·x`, `‖d‖² = p`).  The Eisenstein cubic character is trivial iff the rational
    `r` is a cubic residue mod `p`.  Welds `(·/d)₃` to `ModArith/CubicResidue` — a computable
    `μ₃`-symbol.  ∅-axiom. -/
theorem char_one_iff_rational {d α : ZOmega} {x : Int} {m : Nat} {p : Nat} (hp : 1 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hdp : d.normSq = (p : Int))
    (hred : ModEq d α (ofInt (α.re + α.im * x))) :
    ModEq d (pow α m) (ofInt 1) ↔ (p : Int) ∣ ((α.re + α.im * x) ^ m - 1) :=
  ⟨rational_of_char_one hp hpr hdp hred,
   fun h => char_one_of_rational hred (by rw [hdp]; exact h)⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld
