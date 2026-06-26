import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinYfunGauss

/-!
# The split-prime cube assembly — `g(χ)^{⋆(3(s+1)+1)} = J^{s+1}·p^{s+1}·g(χ)` (∅-axiom)

★★★★★ `gauss_convPow_split` : for a prime `p ≡ 1 (mod 3)` (`p > 3`) and `k < p`,

  `g(χ)^{⋆(3(s+1)+1)}(k) = J^{s+1} · p^{s+1} · g(χ)(k)`   (`J = jacobiSum`).

This is the **cube-side** closed form for a *split* second prime `pr = 3(s+1)+1 ≡ 1 (mod 3)` (the analog
of the inert `gauss_pow_succ_cube`, `g^{⋆(q+1)} = J^{s+1}·p^s·Yfun` for `q+1 = 3(s+1)`).  The extra `⋆g`
(since `pr` is `≡ 1`, not `≡ 0`, mod 3) turns the trailing `Yfun` into `Yfun ⋆ g = p·g`
(`Yfun_conv_gauss`), absorbing one more factor of `p`.

Assembly: `convPow_add` peels `g^{⋆(3(s+1)+1)} = g^{⋆3(s+1)} ⋆ g`; `convPow_mul`/`gauss_convPow3`
/`convPow_scalar`/`Yfun_convPow` compute `g^{⋆3(s+1)} = J^{s+1}·p^s·Yfun` (as in the inert cube);
`conv_scalar_left` twice pulls the scalars out of the outer `⋆g`, and `Yfun_conv_gauss` replaces
`Yfun ⋆ g` by `p·g`.  Evaluated at `k = 1` (`g(1) = χ(1) = 1`) against the split factored Frobenius
`g^{⋆pr}(1) ≡ χ̄(pr)·χ(1)` this gives `J^{s+1}·p^{s+1} ≡ χ̄(pr) (mod ofInt pr)`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitCube

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv conv_congr conv_scalar_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
  (convPow convPow_add convPow_mul convPow_congr convPow_scalar convPow_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv (Yfun)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex (gauss_convPow3 Yfun_convPow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinYfunGauss (Yfun_conv_gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow pow_succ)
open E213.Meta.Algebra213.Ring213 (mul_assoc)

/-- ★★★★★ **The split-prime cube assembly** — `g(χ)^{⋆(3(s+1)+1)}(k) = J^{s+1}·p^{s+1}·g(χ)(k)` for a
    prime `p ≡ 1 (mod 3)` (`p > 3`), `k < p`.  Cube side of the split reciprocity congruence.
    ∅-axiom (PURE). -/
theorem gauss_convPow_split {d : ZOmega} {p m x s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d ZOmega.ZOmega.Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) {k : Nat} (hk : k < p) :
    convPow p (gauss p m x) (3 * (s + 1) + 1) k
      = pow (jacobiSum p m x) (s + 1)
        * (pow (ofInt ((p : Nat) : Int)) (s + 1) * gauss p m x k) := by
  have hp0 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hp1 : 1 ≤ p := Nat.le_of_lt hp
  -- the cube part `g^{⋆3(s+1)}(j) = J^{s+1}·(p^s·Yfun j)`
  have hcube : ∀ j, j < p → convPow p (gauss p m x) (3 * (s + 1)) j
      = pow (jacobiSum p m x) (s + 1) * (pow (ofInt ((p : Nat) : Int)) s * Yfun p j) := by
    intro j hj
    rw [convPow_mul p (gauss p m x) 3 (s + 1) hj,
        convPow_congr p hp0 (fun i hi => gauss_convPow3 hp hp3 hpr h3m hm1 hdn hω hx hi) (s + 1) hj,
        convPow_scalar p (jacobiSum p m x) (Yfun p) (s + 1) hj,
        Yfun_convPow p hp1 s hj]
  -- peel the trailing `⋆g`, rewrite both arguments, pull scalars, apply `Yfun ⋆ g = p·g`
  rw [convPow_add p (gauss p m x) (3 * (s + 1)) 1 hk,
      conv_congr p k hp0 (fun i hi => hcube i hi)
        (fun i hi => convPow_one p (gauss p m x) hi),
      conv_scalar_left p (pow (jacobiSum p m x) (s + 1))
        (fun i => pow (ofInt ((p : Nat) : Int)) s * Yfun p i) (gauss p m x) k,
      conv_scalar_left p (pow (ofInt ((p : Nat) : Int)) s) (Yfun p) (gauss p m x) k,
      Yfun_conv_gauss hp hp3 hpr h3m hm1 hdn hω hx hk,
      ← mul_assoc (pow (ofInt ((p : Nat) : Int)) s) (ofInt ((p : Nat) : Int)) (gauss p m x k),
      ← pow_succ]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitCube
