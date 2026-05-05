import E213.Math.Cohomology.Hodge.Star

import E213.Math.Cohomology.Cochain.Core
import E213.Physics.Simplex.Counts
/-!
# Cohomology — ⋆⋆ = id (, file 2)

In ℤ/2 cohomology the Hodge star is an involution:
  ⋆ : Cᵏ → Cⁿ⁻ᵏ,   ⋆⋆ : Cᵏ → Cᵏ
  (⋆⋆σ)(i) = σ(complement (complement i)) = σ(i).

All cochains here use **explicit Bool returns** (`== 0`, `true`).
Definitions via `Prop` coercion (`fun i => i.val = 0`) trigger
elaboration errors when chained through `hodgeStar` (Nat-sub
in result type).
-/

namespace E213.Math.Cohomology.Hodge.Involution

open E213.Physics.Simplex.Counts (binom d NS NT)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Hodge.Star (hodgeStar)

/-- Vertex-0 indicator on n=5, Bool-pure. -/
def v0_5 : Cochain 5 1 := fun i => i.val == 0

/-- Edge-0 indicator on n=5 (colex idx 0 = [0,1]). -/
def e0_5 : Cochain 5 2 := fun i => i.val == 0

/-- All-true cochain at (5, 2). -/
def all_true_5_2 : Cochain 5 2 := fun _ => true

/-- All-true cochain at (3, 1). -/
def at_3_1_h : Cochain 3 1 := fun _ => true

/-- ⋆⋆(zero) at (5, 1). -/
theorem hodge_sq_zero_5_1 :
    ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 (Cochain.zero 5 1)) i
        = (Cochain.zero 5 1) i := by decide

/-- ⋆⋆(zero) at (5, 2). -/
theorem hodge_sq_zero_5_2 :
    ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 (Cochain.zero 5 2)) i
        = (Cochain.zero 5 2) i := by decide

/-- ⋆⋆(v0_5) = v0_5. -/
theorem hodge_sq_v0_5 :
    ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 v0_5) i = v0_5 i := by decide

/-- ⋆⋆(e0_5) = e0_5. -/
theorem hodge_sq_e0_5 :
    ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 e0_5) i = e0_5 i := by decide

/-- ⋆⋆(all_true_5_2) = all_true_5_2. -/
theorem hodge_sq_all_true_5_2 :
    ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 all_true_5_2) i = all_true_5_2 i := by decide

/-- ⋆⋆(at_3_1_h) = at_3_1_h. -/
theorem hodge_sq_at_3_1_h :
    ∀ i : Fin (binom 3 1),
      hodgeStar 3 2 1 (hodgeStar 3 1 2 at_3_1_h) i = at_3_1_h i := by decide

/-- ★ intermediate capstone — ⋆⋆ = id on Δ⁴, bundled. -/
theorem phase_CB_hodge_involution :
    (∀ i : Fin (binom 5 1), hodgeStar 5 4 1 (hodgeStar 5 1 4 v0_5) i = v0_5 i)
    ∧ (∀ i : Fin (binom 5 2), hodgeStar 5 3 2 (hodgeStar 5 2 3 e0_5) i = e0_5 i)
    ∧ (∀ i : Fin (binom 5 2),
         hodgeStar 5 3 2 (hodgeStar 5 2 3 all_true_5_2) i = all_true_5_2 i) :=
  ⟨hodge_sq_v0_5, hodge_sq_e0_5, hodge_sq_all_true_5_2⟩

end E213.Math.Cohomology.Hodge.Involution
