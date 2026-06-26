import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
import E213.Lib.Math.NumberTheory.EulerTheorem

/-!
# Reducing the Jacobi-sum norm by the unit-multiplication reindex (∅-axiom)

The list-sum reindex that drives `N(J) = J·J̄ = p`.  For a unit `a` (`gcd(a,p)=1`), multiplication
`s ↦ (a·s) mod p` **permutes** `totativeList p` (`EulerTheorem.lperm_image`), so any sum over the
totatives is invariant under it:

  `Σ_{s ∈ tot} G(s) = Σ_{s ∈ tot} G((a·s) mod p)`   (`listSum_reindex_mul`).

Combined with the conjugate per-term identity `χ_ω(a)·χ̄_ω((a·s) mod p) = χ̄_ω(s)`
(`chiOmega_reindex_conj`, the `conj` sibling of `chiOmega_reindex`), the inner `b`-sum of
`jacobiList_norm_double` reindexes (`b = a·s`) so the `χ_ω(a)·χ̄_ω(b)` pairing collapses to `χ̄_ω(s)`.
This is the engine of the `N(J)=p` reduction (A3 step 4–5).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReduce

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_lperm listSum_map listSum_congr)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList_pos totativeList_le totativeList_coprime totative_lt_n)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex (chiOmega_reindex)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList lperm_image)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Meta.Algebra213.Ring213 (mul_assoc)

/-- ★★★★ **Unit-multiplication reindex of a totative sum** — `Σ_{s∈tot} G(s) = Σ_{s∈tot} G((a·s)%p)`
    for a unit `a`.  `s ↦ (a·s)%p` permutes `totativeList p` (`lperm_image`); `listSum_lperm` +
    `listSum_map`.  ∅-axiom. -/
theorem listSum_reindex_mul {p a : Nat} (hp : 1 < p)
    (ha : E213.Tactic.NatHelper.gcd213 a p = 1) (G : Nat → ZOmega) :
    listSum G (totativeList p) = listSum (fun s => G ((a * s) % p)) (totativeList p) := by
  rw [listSum_lperm G (lperm_image hp ha)]
  exact listSum_map G (fun s => (a * s) % p) (totativeList p)

/-- ★★★★ **The conjugate reindex identity** — `χ_ω(a)·conj χ_ω((a·s)%p) = conj χ_ω(s)` for units
    `a, s`.  The `conj` of `chiOmega_reindex` (`χ_ω((a·s)%p)·conj χ_ω(a) = χ_ω(s)`), using `conj_mul` +
    `conj_conj`.  Under `b = a·s` this collapses the `χ_ω(a)·χ̄_ω(b)` pairing of the norm double-sum.
    ∅-axiom. -/
theorem chiOmega_reindex_conj {d : ZOmega} {p m x a s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ha1 : 0 < a) (halt : a < p) (hs1 : 0 < s) (hslt : s < p) :
    chiOmega p m x a * conj (chiOmega p m x ((a * s) % p)) = conj (chiOmega p m x s) := by
  have hre := chiOmega_reindex hp hp3 hpr h3m hdn hω hx ha1 halt hs1 hslt
  -- hre : χ_ω((a·s)%p) · conj χ_ω(a) = χ_ω(s)
  have hc := congrArg conj hre
  rw [conj_mul, conj_conj] at hc
  -- hc : conj χ_ω((a·s)%p) · χ_ω(a) = conj χ_ω(s)
  rw [ZOmega.mul_comm]; exact hc

/-- **4-factor rearrangement** — `(A·B)·(C·D) = B·((A·C)·D)` in `ℤ[ω]` (commutative ring). -/
theorem rearr4 (A B C D : ZOmega) : A * B * (C * D) = B * (A * C * D) := by
  rw [ZOmega.mul_comm A B, mul_assoc, ← mul_assoc A C D]

/-- ★★★★ **The reindexed inner term** — after `b = (a·s) mod p`, the norm double-sum term
    `(χ_ω(a)χ_ω(1−a))·(χ̄_ω((a·s)%p)χ̄_ω(1−as))` collapses to `χ_ω(1−a)·(χ̄_ω(s)·χ̄_ω(1−as))`: the
    `χ_ω(a)·χ̄_ω((a·s)%p) = χ̄_ω(s)` pairing (`chiOmega_reindex_conj`) after `rearr4`.  ∅-axiom. -/
theorem jacobi_inner_term {d : ZOmega} {p m x a s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ha1 : 0 < a) (halt : a < p) (hs1 : 0 < s) (hslt : s < p) :
    chiOmega p m x a * chiOmega p m x ((1 + (p - a)) % p)
        * (conj (chiOmega p m x ((a * s) % p))
            * conj (chiOmega p m x ((1 + (p - (a * s) % p)) % p)))
      = chiOmega p m x ((1 + (p - a)) % p)
        * (conj (chiOmega p m x s) * conj (chiOmega p m x ((1 + (p - (a * s) % p)) % p))) := by
  rw [rearr4, chiOmega_reindex_conj hp hp3 hpr h3m hdn hω hx ha1 halt hs1 hslt]

/-- ★★★★★ **The inner-sum reduction** — for a fixed unit `a`, the inner `b`-sum of the norm
    double-sum reindexes (`b = (a·s) mod p`) and collapses termwise to

      `Σ_{s∈tot} χ_ω(1−a)·(χ̄_ω(s)·χ̄_ω((1−as) mod p))`.

    `listSum_reindex_mul` (the unit-permutation) + `listSum_congr` with `jacobi_inner_term`.  This is
    the inner half of `J·J̄ = Σ_a χ_ω(1−a)·Σ_s χ̄_ω(s)·χ̄_ω(1−as)` — the form whose `s`-sum
    (`S(b)`-type) the final collapse evaluates.  ∅-axiom. -/
theorem jacobi_inner_reduce {d : ZOmega} {p m x a : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ha : E213.Tactic.NatHelper.gcd213 a p = 1) (ha1 : 0 < a) (halt : a < p) :
    listSum (fun b => chiOmega p m x a * chiOmega p m x ((1 + (p - a)) % p)
        * (conj (chiOmega p m x b) * conj (chiOmega p m x ((1 + (p - b)) % p)))) (totativeList p)
      = listSum (fun s => chiOmega p m x ((1 + (p - a)) % p)
        * (conj (chiOmega p m x s)
            * conj (chiOmega p m x ((1 + (p - (a * s) % p)) % p)))) (totativeList p) := by
  rw [listSum_reindex_mul hp ha]
  refine listSum_congr (totativeList p) (fun s hs => ?_)
  have hs1 : 0 < s := totativeList_pos hs
  have hslt : s < p :=
    totative_lt_n hp (totativeList_coprime hs) (totativeList_pos hs) (totativeList_le hs)
  exact jacobi_inner_term hp hp3 hpr h3m hdn hω hx ha1 halt hs1 hslt

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReduce
