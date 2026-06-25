import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
import E213.Lib.Math.NumberTheory.EulerTheorem

/-!
# Reducing the Jacobi-sum norm by the unit-multiplication reindex (∅-axiom, Phase A3)

The list-sum reindex that drives `N(J) = J·J̄ = p`.  For a unit `a` (`gcd(a,p)=1`), multiplication
`s ↦ (a·s) mod p` **permutes** `totativeList p` (`EulerTheorem.lperm_image`), so any sum over the
totatives is invariant under it:

  `Σ_{s ∈ tot} G(s) = Σ_{s ∈ tot} G((a·s) mod p)`   (`listSum_reindex_mul`).

Combined with the conjugate per-term identity `χ_ω(a)·χ̄_ω((a·s) mod p) = χ̄_ω(s)`
(`chiOmega_reindex_conj`, the `conj` sibling of `chiOmega_reindex`), the inner `b`-sum of
`jacobiList_norm_double` reindexes (`b = a·s`) so the `χ_ω(a)·χ̄_ω(b)` pairing collapses to `χ̄_ω(s)`.
This is the engine of the `N(J)=p` reduction (`research-notes/frontiers/higher_reciprocity_roadmap.md`,
A3 step 4–5).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReduce

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_lperm listSum_map)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex (chiOmega_reindex)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList lperm_image)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)

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
  rw [mul_comm]; exact hc

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReduce
