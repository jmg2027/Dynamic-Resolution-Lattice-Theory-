import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumRange
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm

/-!
# The norm-Gauss convolution `Yfun ⋆ g(χ) = p · g(χ)` (∅-axiom)

★★★★★ `Yfun_conv_gauss` : for a prime `p ≡ 1 (mod 3)` (`p > 3`) and `k < p`,

  `(Yfun p ⋆ g(χ))(k) = ofInt(p) · g(χ)(k)`.

`Yfun = p·δ₀ − allones` (`Y_decomp`: `Yfun = (−1) + Bfun`, `Bfun = p·δ₀`).  The `−1` part contributes
`(−1)·Σ_i g((k+p−i)%p) = (−1)·Σ_t g(t) = 0` by the **character orthogonality** `Σ_t χ_ω(t) = 0`
(`chiOmega_sumRange_zero`), after the reflection reindex `i ↦ (k+p−i)%p` (`rangeList_refl_lperm`); the
`Bfun = p·δ₀` part contributes the single term `p·g(k)`.

This is the cube-side identity of the **split-prime** cubic-reciprocity assembly: with `g(χ)^{⋆3} = J·Yfun`
and `Yfun^{⋆s} = p^{s−1}·Yfun`, it gives `g(χ)^{⋆pr} = J^s·p^s·g(χ)` for a split prime `pr = 3s+1`, the
analog of the inert `g^{⋆(q+1)} = J^{s+1}·p^s·Yfun`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinYfunGauss

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv (Yfun Bfun Bfun_zero Y_decomp)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumRange (chiOmega_sumRange_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sum_congr sum_add sum_mul_left sum_single)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_map listSum_lperm)
open E213.Lib.Math.Combinatorics.RangeList (rangeList)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (sumRange_eq_listSum add_p_mod)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm (rangeList_refl_lperm)
open E213.Meta.Algebra213.Ring213 (mul_zero zero_mul zero_add add_mul)

/-- ★★★★★ **`Yfun ⋆ g(χ) = p·g(χ)`** (coefficient form) — for a prime `p ≡ 1 (mod 3)` (`p > 3`), `k < p`.
    The `−1` part of `Yfun` vanishes by character orthogonality; the `p·δ₀` part gives `p·g(k)`.
    ∅-axiom (PURE). -/
theorem Yfun_conv_gauss {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) {k : Nat} (hk : k < p) :
    conv p (Yfun p) (gauss p m x) k = ofInt ((p : Nat) : Int) * gauss p m x k := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hp1 : 1 ≤ p := Nat.le_of_lt hp
  -- the reflection reindex collapses `Σ_i g((k+p−i)%p)` to `Σ_t g(t) = 0`
  have hrefl0 : sumRange (fun i => gauss p m x ((k + p - i) % p)) p = 0 := by
    rw [sumRange_eq_listSum, ← listSum_map (gauss p m x) (fun i => (k + p - i) % p) (rangeList p),
        ← listSum_lperm (gauss p m x) (rangeList_refl_lperm hppos hk), ← sumRange_eq_listSum]
    exact chiOmega_sumRange_zero hp hp3 hpr h3m hm1 hdn hω hx
  show sumRange (fun i => Yfun p i * gauss p m x ((k + p - i) % p)) p = _
  -- split each summand `Yfun(i)·g = (−1)·g + Bfun(i)·g`
  rw [sum_congr p (fun i _ => by rw [Y_decomp hp1 i, add_mul]), sum_add]
  -- S₁ = (−1)·Σ g = 0
  rw [show sumRange (fun i => ofInt (-1) * gauss p m x ((k + p - i) % p)) p = 0 from by
        rw [sum_mul_left (ofInt (-1)) (fun i => gauss p m x ((k + p - i) % p)) p, hrefl0, mul_zero]]
  -- S₂ = Bfun(0)·g(k) = p·g(k)  (single point i = 0)
  rw [show sumRange (fun i => Bfun p i * gauss p m x ((k + p - i) % p)) p
        = ofInt ((p : Nat) : Int) * gauss p m x k from by
        rw [sum_single p 0 hppos _ (fun i _ hne => by
              show Bfun p i * gauss p m x ((k + p - i) % p) = 0
              unfold Bfun; rw [if_neg hne, zero_mul])]
        show Bfun p 0 * gauss p m x ((k + p - 0) % p) = _
        rw [Bfun_zero, Nat.sub_zero, add_p_mod hppos k, Nat.mod_eq_of_lt hk]]
  rw [zero_add]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinYfunGauss
