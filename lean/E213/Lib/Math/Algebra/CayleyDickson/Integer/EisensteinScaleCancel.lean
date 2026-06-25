import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Meta.Int213.PolyIntMTactic

/-!
# The endgame cancellation — a `μ₃`-scaled fixed sum is zero (∅-axiom, Phase A3)

The last step of cubic-character orthogonality.  If a sum `S ∈ ℤ[ω]` is **fixed by a nontrivial
`μ₃`-scaling**, `w·S = S` with `w ≠ 1`, then `S = 0`:

  `(w − 1)·S = w·S − S = S − S = 0`,  and `ℤ[ω]` is an **integral domain** (`ZOmegaDomain.no_zero_div`),
  so `w − 1 = 0` or `S = 0`; the former is excluded.

This is exactly the shape `Σ_t χ_ω(t) = χ_ω(a)·Σ_t χ_ω(t)` takes once the scaling invariance
`Σ_t χ_ω(t) = Σ_t χ_ω(a·t)` (`chiOmega_mul` + the unit-permutation reindexing) is in hand: with `a` a
non-cubic-residue, `χ_ω(a) ∈ {ω, ω²} ≠ 1`, so the character sum vanishes (`research-notes/frontiers/
higher_reciprocity_roadmap.md`, Phase A3).  Supporting ring identities `sub_mul_zomega`,
`one_mul_zomega`, `sub_self_zomega` are proved componentwise (`ext` + pure `Int213`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt no_zero_div)
open E213.Meta.Int213.Order (sub_self_zero sub_zero)
open E213.Meta.Int213.PolyIntM (one_mulZ)
open E213.Meta.Int213 (zero_mul zero_add add_comm)
open E213.Meta.Algebra213.Ring213 (add_assoc add_zero neg_add_cancel_self)

/-- Pure `a + 0 = a` over `ℤ`. -/
private theorem int_add_zero (a : Int) : a + 0 = a := by rw [add_comm, zero_add]

/-- **Right distributivity over subtraction** — `(a − b)·c = a·c − b·c` in `ℤ[ω]`.  Componentwise
    `ring_intZ`. -/
theorem sub_mul_zomega (a b c : ZOmega) : (a - b) * c = a * c - b * c := by
  refine ZOmega.ext ?_ ?_
  · show (a.re - b.re) * c.re - (a.im - b.im) * c.im
       = (a.re * c.re - a.im * c.im) - (b.re * c.re - b.im * c.im)
    ring_intZ
  · show (a.re - b.re) * c.im + (a.im - b.im) * c.re - (a.im - b.im) * c.im
       = (a.re * c.im + a.im * c.re - a.im * c.im) - (b.re * c.im + b.im * c.re - b.im * c.im)
    ring_intZ

/-- **`1 · S = S`** in `ℤ[ω]` (`ofInt 1 = ⟨1,0⟩`). -/
theorem one_mul_zomega (S : ZOmega) : ofInt 1 * S = S := by
  refine ZOmega.ext ?_ ?_
  · show (1 : Int) * S.re - 0 * S.im = S.re
    rw [one_mulZ, zero_mul, sub_zero]
  · show (1 : Int) * S.im + 0 * S.re - 0 * S.im = S.im
    rw [one_mulZ, zero_mul, zero_mul, sub_zero, int_add_zero]

/-- **`S − S = 0`** in `ℤ[ω]`. -/
theorem sub_self_zomega (S : ZOmega) : S - S = 0 := by
  refine ZOmega.ext ?_ ?_
  · show S.re - S.re = 0
    exact sub_self_zero S.re
  · show S.im - S.im = 0
    exact sub_self_zero S.im

/-- **`u − v = 0 ⟹ u = v`** in `ℤ[ω]`. -/
theorem eq_of_sub_eq_zero {u v : ZOmega} (h : u - v = 0) : u = v := by
  have h' : u + -v = 0 := h
  have e : u + -v + v = u := by
    rw [add_assoc, neg_add_cancel_self, add_zero]
  rw [h', E213.Meta.Algebra213.Ring213.zero_add] at e
  exact e.symm

/-- ★★★★ **A `μ₃`-scaled fixed sum vanishes.**  If `w·S = S` with `w ≠ 1`, then `S = 0`:
    `(w−1)·S = w·S − S = S − S = 0` and `ℤ[ω]` has no zero divisors.  The final step of
    `Σ_t χ_ω(t) = 0` (scaling invariance under a non-residue `a`, `w = χ_ω(a) ∈ {ω,ω²}`).  ∅-axiom. -/
theorem scale_fixed_eq_zero {w S : ZOmega} (hw : w ≠ ofInt 1) (h : w * S = S) : S = 0 := by
  have key : (w - ofInt 1) * S = 0 := by
    rw [sub_mul_zomega, one_mul_zomega, h, sub_self_zomega]
  rcases no_zero_div (w - ofInt 1) S key with h1 | h2
  · exact absurd (eq_of_sub_eq_zero h1) hw
  · exact h2

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel
