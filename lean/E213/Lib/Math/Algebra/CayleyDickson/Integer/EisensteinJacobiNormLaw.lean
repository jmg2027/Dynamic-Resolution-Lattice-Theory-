import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussNormSq
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSqZero
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConjConv
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiTerm

/-!
# The Jacobi-sum norm law `N(J) = p` (∅-axiom, Phase A3 / route b — THE GOAL)

The cubic Jacobi sum has norm `p`:

  `(jacobiSum p m x).normSq = p`   (`jacobi_norm`).

Read the `e_1`-coefficient of `(g·g)⋆(ḡ·ḡ)` two ways.  **One way** (`gg_gbgb_eq`):
`= ofInt(↑p)·Yfun 1 = ofInt(↑p)·ofInt(−1)`.  **The other** (`gauss_sq_full` for `g·g`,
`gbgb_eq_conj_gg`+`gauss_sq_full` for `ḡ·ḡ`): each term factors as `(J·conj J)·(conj χ(i)·χ((i+p−1)%p))`
(`conj χ(t)²=χ(t)`), so the sum is `(J·conj J)·Σ conj χ(i)·χ((i+p−1)%p) = (J·conj J)·ofInt(−1)`
(`chi2_offdiag_one`, the conjugate of the off-diagonal `−1`).  Cancelling `ofInt(−1)`:
`J·conj J = ofInt(↑p)`, and `J·conj J = ofInt(‖J‖²)` (`mul_conj_self`), so `‖J‖² = p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj conj_mul conj_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag (gauss_offdiag_sum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne (gauss_conj_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv (Yfun)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussNormSq (gg_gbgb_eq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSqZero (gauss_sq_full)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConjConv (gbgb_eq_conj_gg conj_sumRange)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag (conv_offdiag_index)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq (conj_chiOmega_eq_sq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiTerm (mul_swap_mid)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (mul_left_cancel_zomega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_congr sum_mul_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (mul_comm)

/-- `conj (χ_ω(t)·χ_ω(t)) = χ_ω(t)` — `χ(t)²` is `conj χ(t)`, so `conj` of it is `χ(t)`. -/
theorem conj_sq_chiOmega (p m x t : Nat) :
    conj (chiOmega p m x t * chiOmega p m x t) = chiOmega p m x t := by
  rw [← conj_chiOmega_eq_sq, conj_conj]

/-- The conjugate off-diagonal at `e_1` — `Σ_i conj χ_ω(i)·χ_ω((i+p−1)%p) = ofInt(−1)`.  The `conj` of
    `(g⋆ḡ)(1) = −1` (`gauss_offdiag_sum`/`gauss_conj_norm`).  ∅-axiom. -/
theorem chi2_offdiag_one {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    sumRange (fun i => conj (chiOmega p m x i) * chiOmega p m x ((i + p - 1) % p)) p = ofInt (-1) := by
  have h1p : 1 < p := hp
  have heq : sumRange (fun i => chiOmega p m x i * conj (chiOmega p m x ((i + p - 1) % p))) p
      = ofInt (-1) := by
    rw [← gauss_offdiag_sum h1p, gauss_conj_norm hp hp3 hpr h3m hm1 hdn hω hx h1p, if_neg (by decide)]
  calc sumRange (fun i => conj (chiOmega p m x i) * chiOmega p m x ((i + p - 1) % p)) p
      = sumRange (fun i => conj (chiOmega p m x i * conj (chiOmega p m x ((i + p - 1) % p)))) p :=
        sum_congr p (fun i _ => by rw [conj_mul, conj_conj])
    _ = conj (sumRange (fun i => chiOmega p m x i * conj (chiOmega p m x ((i + p - 1) % p))) p) :=
        (conj_sumRange _ _).symm
    _ = conj (ofInt (-1)) := by rw [heq]
    _ = ofInt (-1) := by decide

/-- ★★★★★★ **The Jacobi-sum norm law** — `N(J) = (jacobiSum p m x).normSq = p` for a prime `p ≡ 1 mod 3`
    (`p > 3`), `m=(p−1)/3`, with a cube root `x` of unity (`p ∣ x²+x+1`) and an Eisenstein prime `d` of
    norm `p`.  The `e_1`-coefficient of `(g·g)⋆(ḡ·ḡ)` read two ways.  ∅-axiom. -/
theorem jacobi_norm {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    (jacobiSum p m x).normSq = (p : Int) := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have h1p : 1 < p := hp
  -- per-term factoring of the e_1 summand
  have hterm : ∀ i, i < p →
      conv p (gauss p m x) (gauss p m x) i * conv p (gaussConj p m x) (gaussConj p m x) ((1 + p - i) % p)
        = (jacobiSum p m x * conj (jacobiSum p m x))
          * (conj (chiOmega p m x i) * chiOmega p m x ((i + p - 1) % p)) := by
    intro i hi
    have hw : (p - (1 + p - i) % p) % p = (i + p - 1) % p := conv_offdiag_index h1p hi
    rw [gauss_sq_full hp hp3 hpr h3m hm1 hdn hω hx hi,
        gbgb_eq_conj_gg (Nat.mod_lt _ hp0), hw,
        gauss_sq_full hp hp3 hpr h3m hm1 hdn hω hx (Nat.mod_lt _ hp0),
        conj_mul, conj_sq_chiOmega p m x ((i + p - 1) % p),
        ← conj_chiOmega_eq_sq p m x i]
    exact mul_swap_mid (jacobiSum p m x) (conj (chiOmega p m x i)) (conj (jacobiSum p m x))
      (chiOmega p m x ((i + p - 1) % p))
  -- the e_1 coefficient = (J·conj J)·(−1)
  have hsum : conv p (fun j => conv p (gauss p m x) (gauss p m x) j)
        (fun j => conv p (gaussConj p m x) (gaussConj p m x) j) 1
      = (jacobiSum p m x * conj (jacobiSum p m x)) * ofInt (-1) := by
    show sumRange (fun i => conv p (gauss p m x) (gauss p m x) i
          * conv p (gaussConj p m x) (gaussConj p m x) ((1 + p - i) % p)) p = _
    rw [sum_congr p (fun i hi => hterm i hi),
        sum_mul_left (jacobiSum p m x * conj (jacobiSum p m x))
          (fun i => conj (chiOmega p m x i) * chiOmega p m x ((i + p - 1) % p)) p,
        chi2_offdiag_one hp hp3 hpr h3m hm1 hdn hω hx]
  -- the same e_1 coefficient = ofInt(↑p)·(−1)
  have hgg := gg_gbgb_eq hp hp3 hpr h3m hm1 hdn hω hx h1p
  have hY1 : Yfun p 1 = ofInt (-1) := by unfold Yfun; rw [if_neg (by decide)]
  rw [hY1] at hgg
  -- (J·conj J)·ofInt(−1) = ofInt(↑p)·ofInt(−1)  ⟹  J·conj J = ofInt(↑p)
  have hcancel : jacobiSum p m x * conj (jacobiSum p m x) = ofInt ((p : Nat) : Int) := by
    have he : ofInt (-1) * (jacobiSum p m x * conj (jacobiSum p m x))
        = ofInt (-1) * ofInt ((p : Nat) : Int) := by
      rw [mul_comm (ofInt (-1)) (jacobiSum p m x * conj (jacobiSum p m x)),
          mul_comm (ofInt (-1)) (ofInt ((p : Nat) : Int)), ← hsum, ← hgg]
    exact mul_left_cancel_zomega (by decide) he
  -- J·conj J = ofInt(‖J‖²)
  rw [mul_conj_self (jacobiSum p m x)] at hcancel
  exact congrArg ZOmega.ZOmega.re hcancel

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw
