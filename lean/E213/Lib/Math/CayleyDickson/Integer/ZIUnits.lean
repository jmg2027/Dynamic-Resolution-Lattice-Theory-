import E213.Lib.Math.CayleyDickson.Integer.ZIAlgebra213
import E213.Meta.Int213.Bound

/-!
# ZIUnits — the Gaussian integer unit group `ℤ[i]^×` has order 4 (the 4-theorem)

The 2-axis companion to `ZOmegaUnits` (Eisenstein, order 6).  `ℤ[i]^× = {±1, ±i}` has
**order 4**, the square-lattice unit group, between `ℤ^×` (order 2) and `ℤ[ω]^×`
(order 6).  These three are the *only* imaginary-quadratic unit-group orders (Dirichlet:
the free rank is 0, so the units are the roots of unity, and `φ(m) ≤ 2` forces
`m ∈ {1,2,3,4,6}`, i.e. orders `{2, 4, 6}`).

  * `units4` — the four units explicitly; `units4_length = 4`, `units4_nodup`.
  * `units4_normSq_one` — each has `‖·‖² = 1`.
  * ★★★ `normSq_one_in_units4` — Diophantine completeness: every `u : ℤ[i]` with
    `‖u‖² = 1` is one of the four (`re² + im² = 1` bounds `re, im ∈ {−1,0,1}`).
  * ★★★★ `ZI_units_exact_four` — `|ℤ[i]^×| = 4` exactly.

All zero-axiom.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZI

open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI

/-! ## §1 — the four units -/

/-- The four Gaussian units `{1, −1, i, −i}`. -/
def units4 : List ZI := [⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]

theorem units4_length : units4.length = 4 := rfl

theorem units4_nodup : units4.Nodup := by decide

/-- Each of the four listed units has `normSq = 1`. -/
theorem units4_normSq_one : ∀ u ∈ units4, u.normSq = 1 := by decide

/-! ## §2 — Diophantine completeness -/

private theorem re_sq_le_one (u : ZI) (h : u.normSq = 1) : u.re * u.re ≤ 1 := by
  have h' : u.im * u.im + u.re * u.re = 1 := by
    have h0 : u.re * u.re + u.im * u.im = 1 := h
    rw [E213.Meta.Int213.add_comm (u.im * u.im) (u.re * u.re)]; exact h0
  exact E213.Meta.Int213.le_of_add_eq_of_nonneg h' (E213.Meta.Int213.int_sq_nonneg u.im)

private theorem im_sq_le_one (u : ZI) (h : u.normSq = 1) : u.im * u.im ≤ 1 := by
  have h' : u.re * u.re + u.im * u.im = 1 := h
  exact E213.Meta.Int213.le_of_add_eq_of_nonneg h' (E213.Meta.Int213.int_sq_nonneg u.re)

/-- ★★★ **Diophantine completeness**: every Gaussian integer of norm `1` is one of the
    four units.  `re² + im² = 1` over `ℤ` bounds `re, im ∈ {−1,0,1}`; the nine candidates
    leave exactly the four. -/
theorem normSq_one_in_units4 (u : ZI) (h : u.normSq = 1) :
    units4.contains u = true := by
  have h_re := E213.Meta.Int213.int_sq_le_one u.re (re_sq_le_one u h)
  have h_im := E213.Meta.Int213.int_sq_le_one u.im (im_sq_le_one u h)
  have h_u_form : u = ⟨u.re, u.im⟩ := by cases u; rfl
  rcases h_re with h_re_eq | h_re_eq | h_re_eq <;>
    rcases h_im with h_im_eq | h_im_eq | h_im_eq <;>
    first
      | (rw [h_u_form, h_re_eq, h_im_eq]; decide)
      | (exfalso; rw [h_u_form, h_re_eq, h_im_eq] at h; exact absurd h (by decide))

/-! ## §3 — exact cardinality -/

/-- ★★★★ **`|ℤ[i]^×| = 4` exactly** — the Gaussian 4-theorem. -/
theorem ZI_units_exact_four :
    (∀ u ∈ units4, u.normSq = 1)
    ∧ (∀ u : ZI, u.normSq = 1 → units4.contains u = true)
    ∧ units4.length = 4
    ∧ units4.Nodup :=
  ⟨units4_normSq_one, normSq_one_in_units4, units4_length, units4_nodup⟩

end E213.Lib.Math.CayleyDickson.Integer.ZI
