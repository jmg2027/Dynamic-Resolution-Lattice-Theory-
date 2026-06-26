import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Meta.Int213.PolyIntMTactic

/-!
# The cubic Jacobi sum and its norm `N(J) = J·J̄` — list form (∅-axiom)

The Jacobi sum in the generic `listSum` framework (so the orthogonality/permutation machinery applies),
its conjugate, and the **double-sum form of the norm** `N(J) = J·J̄`:

  `jacobiList = Σ_{a < p} χ_ω(a)·χ_ω((1−a) mod p)`,
  `conj J     = Σ_{a < p} χ̄_ω(a)·χ̄_ω((1−a) mod p)`   (`jacobiList_conj`),
  `J·J̄        = Σ_{a<p} Σ_{b<p} χ_ω(a)χ_ω(1−a)·χ̄_ω(b)χ̄_ω(1−b)`   (`jacobiList_norm_double`).

This sets up `N(J) = p`: the remaining step is the reindexing `a = b·c` collapsing the inner sum by
the character orthogonality `Σ_c χ_ω(c) = 0` (`EisensteinCharSumZero.chiListSum_totatives_zero`) — the
final A3 build.  Supporting: `conj` is a
`listSum` homomorphism (`conj_listSum`, from componentwise `conj_add`/`conj_zero`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_cons listSum_mul_distrib)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList)

/-- `conj 0 = 0` in `ℤ[ω]`. -/
theorem conj_zero : conj (0 : ZOmega) = 0 := rfl

/-- `conj (u + v) = conj u + conj v` in `ℤ[ω]`. -/
theorem conj_add (u v : ZOmega) : conj (u + v) = conj u + conj v := by
  refine ZOmega.ext ?_ ?_
  · show (u.re + v.re) - (u.im + v.im) = (u.re - u.im) + (v.re - v.im); ring_intZ
  · show -(u.im + v.im) = -u.im + -v.im; ring_intZ

/-- ★★★ **`conj` is a `listSum` homomorphism** — `conj (Σ_L f) = Σ_L (conj ∘ f)`.  Induction with
    `conj_add` / `conj_zero`. -/
theorem conj_listSum (f : Nat → ZOmega) : ∀ (L : List Nat),
    conj (listSum f L) = listSum (fun t => conj (f t)) L
  | [] => conj_zero
  | t :: l => by
      show conj (f t + listSum f l) = conj (f t) + listSum (fun t => conj (f t)) l
      rw [conj_add, conj_listSum f l]

/-- The cubic Jacobi sum as a `listSum`: `J = Σ_{a < p} χ_ω(a)·χ_ω((1−a) mod p)`. -/
def jacobiList (p m x : Nat) : ZOmega :=
  listSum (fun a => chiOmega p m x a * chiOmega p m x ((1 + (p - a)) % p)) (totativeList p)

/-- ★★★ **The conjugate Jacobi sum** — `conj J = Σ_{a<p} χ̄_ω(a)·χ̄_ω((1−a) mod p)`.  `conj` distributes
    over the `listSum` (`conj_listSum`) and over each product (`conj_mul`).  ∅-axiom. -/
theorem jacobiList_conj (p m x : Nat) :
    conj (jacobiList p m x)
      = listSum (fun a => conj (chiOmega p m x a) * conj (chiOmega p m x ((1 + (p - a)) % p)))
          (totativeList p) := by
  rw [jacobiList, conj_listSum]
  refine E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum.listSum_congr (totativeList p)
    (fun a _ => ?_)
  exact conj_mul _ _

/-- ★★★★ **The Jacobi-sum norm as a double sum** — `J·J̄ = Σ_{a<p} Σ_{b<p} (χ_ω(a)χ_ω(1−a)) ·
    (χ̄_ω(b)χ̄_ω(1−b))`.  `listSum_mul_distrib` applied to `J` and `conj J`.  The form the orthogonality
    collapse turns into `N(J) = p`.  ∅-axiom. -/
theorem jacobiList_norm_double (p m x : Nat) :
    jacobiList p m x * conj (jacobiList p m x)
      = listSum (fun a => listSum (fun b =>
          (chiOmega p m x a * chiOmega p m x ((1 + (p - a)) % p))
            * (conj (chiOmega p m x b) * conj (chiOmega p m x ((1 + (p - b)) % p))))
          (totativeList p)) (totativeList p) := by
  rw [jacobiList_conj, jacobiList]
  exact listSum_mul_distrib _ _ (totativeList p) (totativeList p)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm
