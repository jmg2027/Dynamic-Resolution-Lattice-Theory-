import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum

/-!
# Cubic-character orthogonality over `[0,p)` — `Σ_{t<p} χ_ω(t) = 0` (∅-axiom)

★★★★★ `chiOmega_sumRange_zero` : the full **`sumRange`-form** character orthogonality —

  `Σ_{t<p} χ_ω(t) = 0`   for a prime `p ≡ 1 (mod 3)`, `p > 3`.

The `chiListSum`/totative version (`EisensteinCharSumZero.chiListSum_totatives_zero`) is over the unit
list; this is the group-ring-native form over `[0,p)` (the convolution `⋆` is built on `sumRange`).  Same
scaling argument, done directly on `sumRange`: a primitive root `g` is a non-cubic-residue (`χ_ω(g) ≠ 1`),
and `t ↦ (g·t)%p` permutes **all** of `[0,p)` (`rangeList_mul_lperm`, including `0 ↦ 0` since `χ_ω(0)=0`),
so `Σ χ_ω = Σ χ_ω((g·t)%p) = χ_ω(g)·Σ χ_ω`; `χ_ω(g) ≠ 1` in the domain `ℤ[ω]` forces the sum to `0`
(`scale_fixed_eq_zero`).

This is the orthogonality behind `allones ⋆ g(χ) = 0`, hence `Yfun ⋆ g(χ) = p·g(χ)` — the cube-side
identity of the **split-prime** cubic-reciprocity assembly.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumRange

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_ne_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (scale_fixed_eq_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_congr sum_mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_map listSum_lperm)
open E213.Lib.Math.Combinatorics.RangeList (rangeList)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
  (sumRange_eq_listSum rangeList_mul_lperm)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar cubicChar_one_iff_cube)
open E213.Lib.Math.NumberTheory.ModArith.CubicResidue (cube_pow_iff_three_dvd_exp)
open E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot (exists_primitive_root)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle (not_dvd_g)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Meta.Nat.NatDiv213 (mul_mod_self_pure)
open E213.Meta.Algebra213.Ring213 (mul_zero)
open E213.Meta.Nat.AddMod213 (zero_mod)

/-- ★★★★★ **Cubic-character orthogonality (`sumRange` form)** — `Σ_{t<p} χ_ω(t) = 0` for a prime
    `p ≡ 1 (mod 3)`, `p > 3`.  Scaling by a primitive root (a non-residue) fixes the sum, forcing it to
    `0` in the domain `ℤ[ω]`.  ∅-axiom (PURE). -/
theorem chiOmega_sumRange_zero {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    sumRange (chiOmega p m x) p = 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  -- a primitive root `g` is a non-cubic-residue, so `χ_ω(g) ≠ 1`
  obtain ⟨g, hg1, hgle, hord⟩ := exists_primitive_root p hp hpr
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  have hgcd : gcd213 g p = 1 := by
    rw [gcd213_comm]; exact prime_coprime p g hpr (not_dvd_g g p hg1 hglt)
  have hnot31 : ¬ (3 ∣ 1) := by
    intro hc; obtain ⟨c, hcc⟩ := hc
    exact absurd (by rw [hcc]; exact mul_mod_self_pure 3 c : (1 : Nat) % 3 = 0) (by decide)
  have hg1pow : g ^ 1 % p = g := by rw [Nat.pow_one, Nat.mod_eq_of_lt hglt]
  have hcne : cubicChar p m g ≠ 1 := by
    intro hc1
    obtain ⟨y, hy1, hylt, hy3⟩ := (cubicChar_one_iff_cube p m g hp hpr h3m hm1 hg1 hglt).mp hc1
    exact hnot31 ((cube_pow_iff_three_dvd_exp p m g hp hpr h3m hm1 hg1 hgle hord 1).mp
      ⟨y, hy1, hylt, by rw [hg1pow]; exact hy3⟩)
  have hanr : chiOmega p m x g ≠ ofInt 1 := chiOmega_ne_one p m x g hg1 hglt hcne
  -- termwise: `χ_ω((g·t)%p) = χ_ω(g)·χ_ω(t)` for every `t < p` (`t = 0`: both sides `0`)
  have hfactor : ∀ t, t < p → chiOmega p m x ((g * t) % p) = chiOmega p m x g * chiOmega p m x t := by
    intro t htlt
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      rw [Nat.mul_zero, zero_mod, chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, mul_zero]
    · exact (chiOmega_mul hp hp3 hpr h3m hdn hω hx hg1 hglt htpos htlt).symm
  -- the scaled sum equals `χ_ω(g)·Σ` (termwise factor + scalar pull) …
  have hA : sumRange (fun t => chiOmega p m x ((g * t) % p)) p
      = chiOmega p m x g * sumRange (chiOmega p m x) p := by
    rw [sum_congr p hfactor]; exact sum_mul_left (chiOmega p m x g) (chiOmega p m x) p
  -- … and equals `Σ` itself (the unit multiplication permutes `[0,p)`)
  have hB : sumRange (fun t => chiOmega p m x ((g * t) % p)) p = sumRange (chiOmega p m x) p := by
    rw [sumRange_eq_listSum, ← listSum_map (chiOmega p m x) (fun i => (g * i) % p) (rangeList p),
        ← listSum_lperm (chiOmega p m x) (rangeList_mul_lperm hppos hgcd),
        ← sumRange_eq_listSum]
  -- so `χ_ω(g)·Σ = Σ` with `χ_ω(g) ≠ 1` ⟹ `Σ = 0`
  exact scale_fixed_eq_zero hanr (by rw [← hA]; exact hB)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumRange
