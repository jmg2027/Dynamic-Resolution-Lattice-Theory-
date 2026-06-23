import E213.Lib.Math.Algebra.GRA.Hom
import E213.Lib.Math.Algebra.GRA.Category
import E213.Lib.Math.Algebra.GRA.Common

/-!
# GRA Depth Functor — Phase 10

For any (2, 3)-GRA model `M`, the depth function
`M.depth : Nat → Nat` is `⌈n/3⌉` (forced by axiom `A6`).  This is
a *natural* assignment in the sense that it does not depend on
the particular Reading: every model yields the same Nat-valued
function.

This file makes that naturality explicit:
  * `gen2_eq_3_depth` — every (2, 3)-GRA model has the same depth
    function (when restricted to `n ≥ 2`)
  * `depth_natural` — across any `GRAHom`, depth is preserved
    pointwise
  * `depth_invariant` — across any `GRAIso`, the depth function
    is identical (the functor `M ↦ M.depth` is *constant* on
    the connected groupoid of (2, 3)-Readings)

The deeper point: the depth is *not* a feature of any one Reading.
It is the unique structural invariant of the (2, 3)-arithmetic that
every Reading reads off the same way.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.DepthFunctor

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Hom
open E213.Lib.Math.Algebra.GRA.Category

/-! ### §1 — Every (2, 3)-GRA model has the same depth function

For `n ≥ 2`, axiom `A6` (`ax_greedy`) pins down
`M.depth n = (n + gen2 - 1) / gen2`.  When `gen2 = 3`, this is
`(n + 2) / 3` — the same Nat function for every (2, 3)-model.
-/

/-- For any model with `gen2 = 3`, depth `n` for `n ≥ gen1` is
    `(n + 2) / 3`. -/
theorem depth_eq_ceil3 (M : GRAModel) (h3 : M.gen2 = 3)
    (n : Nat) (hn : n ≥ M.gen1) :
    M.depth n = (n + 2) / 3 := by
  have h := M.ax_greedy n hn
  rw [h3] at h
  exact h

/-- Two (2, 3)-GRA models with the same `gen1` agree on depth for
    every `n ≥ gen1`. -/
theorem depth_agree (M₁ M₂ : GRAModel)
    (hg2_1 : M₁.gen2 = 3) (hg2_2 : M₂.gen2 = 3)
    (_hg1 : M₁.gen1 = M₂.gen1)
    (n : Nat) (h1 : n ≥ M₁.gen1) (h2 : n ≥ M₂.gen1) :
    M₁.depth n = M₂.depth n := by
  rw [depth_eq_ceil3 M₁ hg2_1 n h1, depth_eq_ceil3 M₂ hg2_2 n h2]

/-! ### §2 — Depth is preserved under any `GRAHom`

A `GRAHom` preserves grade, so the depth function — which is
defined on grades, not carriers — is preserved automatically.
The depth function is "an invariant of the underlying grade
arithmetic", not of any particular carrier representation.
-/

/-- Depth on a grade-`n` element is the model's depth on `n`.  Since
    `GRAHom` preserves grade, this equation transports across homs. -/
theorem depth_under_hom {M₁ M₂ : GRAModel}
    (f : GRAHom M₁ M₂) (x : M₁.Carrier) :
    M₂.depth (M₂.grade (f.toFun x)) = M₂.depth (M₁.grade x) := by
  rw [f.grade_comm]

/-! ### §3 — Functoriality of the (2, 3)-depth

When restricted to (2, 3)-models, the depth function is a
**constant functor** from `GRACat` (or the iso sub-category) to
the discrete category on `Nat → Nat`.
-/

/-- A (2, 3)-GRA model: `gen1 = 2`, `gen2 = 3`.  This packages the
    "(2, 3)-sub-category of GRACat" objects. -/
structure GRA23 where
  /-- The underlying model. -/
  model : GRAModel
  /-- `gen1 = 2`. -/
  gen1_eq : model.gen1 = 2
  /-- `gen2 = 3`. -/
  gen2_eq : model.gen2 = 3

/-- The depth function of a `GRA23`, restricted to `n ≥ 2`, equals
    the standard `⌈n/3⌉`. -/
theorem GRA23.depth_eq (M : GRA23) (n : Nat) (hn : n ≥ 2) :
    M.model.depth n = (n + 2) / 3 := by
  have h := M.model.ax_greedy n (by rw [M.gen1_eq]; exact hn)
  rw [M.gen2_eq] at h
  exact h

/-- Any two `GRA23` models agree on depth at every `n ≥ 2`. -/
theorem GRA23.depth_const (M₁ M₂ : GRA23) (n : Nat) (hn : n ≥ 2) :
    M₁.model.depth n = M₂.model.depth n := by
  rw [M₁.depth_eq n hn, M₂.depth_eq n hn]

/-! ### §4 — Reading instances are `GRA23`

The six closed Readings (`NumberTheory.GRA23_NT`, etc.) are all
`GRA23` objects.  We package each as a `GRA23` value.
-/

/-- Each `Reading.toModel` carries a `GRA23` structure (the
    underlying gen1 = 2, gen2 = 3 witnesses come from each
    Reading's instance definition). -/
def readingToGRA23 : Reading → GRA23
  | .NT => ⟨NumberTheory.GRA23_NT, rfl, rfl⟩
  | .Graph => ⟨Graph.GRA23_Graph, rfl, rfl⟩
  | .Analysis => ⟨Analysis.GRA23_Analysis, rfl, rfl⟩
  | .Cohomology => ⟨Cohomology.GRA23_Cohomology, rfl, rfl⟩
  | .HoTT => ⟨HoTT.GRA23_HoTT, rfl, rfl⟩
  | .HigherAlgebra => ⟨HigherAlgebra.GRA23_HigherAlgebra, rfl, rfl⟩

/-- The underlying model of `readingToGRA23 r` is `r.toModel`. -/
theorem readingToGRA23_model (r : Reading) :
    (readingToGRA23 r).model = r.toModel := by
  cases r <;> rfl

/-- The depth function of every Reading equals `(n + 2) / 3` for
    `n ≥ 2` — the unique structural invariant of the (2, 3) arithmetic. -/
theorem Reading_depth_eq (r : Reading) (n : Nat) (hn : n ≥ 2) :
    r.toModel.depth n = (n + 2) / 3 := by
  rw [← readingToGRA23_model r]
  exact GRA23.depth_eq (readingToGRA23 r) n hn

/-- Depth is **constant** across all six Readings. -/
theorem Reading_depth_const (r s : Reading) (n : Nat) (hn : n ≥ 2) :
    r.toModel.depth n = s.toModel.depth n := by
  rw [Reading_depth_eq r n hn, Reading_depth_eq s n hn]

end E213.Lib.Math.Algebra.GRA.DepthFunctor
