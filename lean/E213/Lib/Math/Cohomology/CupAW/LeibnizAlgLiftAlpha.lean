import E213.Lib.Math.Cohomology.CupAW.Zero
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
import E213.Lib.Math.Cohomology.Bridge.XorPairCombine
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Delta.Linear
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Parametric α-decomp Leibniz lift at (5, 2, b) —  L1 α-side

Mirror of `LeibnizAlgLiftBeta.leibniz_via_β_decomp_general`.  Consolidates
the two α-decomp L1 siblings (`leibniz_via_α_decomp_21` at (5, 2, 1) and
`leibniz_via_α_decomp_22` at (5, 2, 2)) into a single parametric helper
over the right-factor degree `b`.

α-side asymmetry: cup signature `cupAW 5 2 b` produces `Cochain 5 (2 + b - 1)`
where `2 + b` is stuck for abstract `b` (Nat.add recurses on RHS).  The
β-side parametric naturally had `a + 2` (reduces); the α-side needs
explicit `Fin.cast` plumbing on the two RHS indices.  At call sites with
concrete `b ∈ {1, 2}`, the casts reduce to identity by `rfl`.
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftAlpha

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp (decomp_5_2 bz5_2)
open E213.Lib.Math.Cohomology.Bridge.XorPairCombine (combine_10)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left cupAW_add_right)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
  (decomp_step_at_0 decomp_step_at_1 decomp_step_at_2 decomp_step_at_3
   decomp_step_at_4 decomp_step_at_5 decomp_step_at_6 decomp_step_at_7
   decomp_step_at_8 decomp_step_at_9)
open E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
  (delta_cupAW_add_left cupAW_delta_add_left)
open E213.Tactic.NatHelper (cases_lt_ten)

/-- Cast bridging the LHS index `Fin (binom 5 (2 + b - 1 + 1))` to the
    RHS1 index `Fin (binom 5 (3 + b - 1))` (= the index space of
    `cupAW 5 3 b (delta α) β`).  Identity for concrete `b`. -/
@[reducible] def castA (b : Nat) (i : Fin (binom 5 (2 + b - 1 + 1))) :
    Fin (binom 5 (3 + b - 1)) :=
  i.cast (congrArg (binom 5) (by
    rw [Nat.add_comm 2 b, Nat.add_comm 3 b]; rfl))

/-- Cast bridging the LHS index to the RHS2 index
    `Fin (binom 5 (2 + (b+1) - 1))` (= index space of
    `cupAW 5 2 (b+1) α (delta β)`).  Identity for concrete `b`. -/
@[reducible] def castB (b : Nat) (i : Fin (binom 5 (2 + b - 1 + 1))) :
    Fin (binom 5 (2 + (b+1) - 1)) :=
  i.cast (congrArg (binom 5) (by
    rw [Nat.add_comm 2 (b+1), Nat.add_comm 2 b]; rfl))

/-- ★ Parametric α-decomp lens at (5, 2, b).  PURE.

    Generalises `LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21` (b=1)
    and `LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22` (b=2).
    RHS uses `castA/castB` to bridge the Nat.add asymmetry; at concrete
    `b`, casts reduce to identity. -/
theorem leibniz_via_α_decomp_general {b : Nat}
    (α : Cochain 5 2) (β : Cochain 5 b)
    (i : Fin (binom 5 (2 + b - 1 + 1)))
    (h_components : ∀ p : Fin 10,
      delta (cupAW 5 2 b (bz5_2 α p) β) i
        = xor (cupAW 5 3 b (delta (bz5_2 α p)) β (castA b i))
              (cupAW 5 2 (b+1) (bz5_2 α p) (delta β) (castB b i))) :
    delta (cupAW 5 2 b α β) i
      = xor (cupAW 5 3 b (delta α) β (castA b i))
            (cupAW 5 2 (b+1) α (delta β) (castB b i)) := by
  have h_α_pw : ∀ j, α j = decomp_5_2 α j := by
    intro j; rcases j with ⟨n, hn⟩
    rcases (cases_lt_ten hn) with rfl | rfl | rfl | rfl | rfl | rfl
                                | rfl | rfl | rfl | rfl
    · exact (decomp_step_at_0 α).symm
    · exact (decomp_step_at_1 α).symm
    · exact (decomp_step_at_2 α).symm
    · exact (decomp_step_at_3 α).symm
    · exact (decomp_step_at_4 α).symm
    · exact (decomp_step_at_5 α).symm
    · exact (decomp_step_at_6 α).symm
    · exact (decomp_step_at_7 α).symm
    · exact (decomp_step_at_8 α).symm
    · exact (decomp_step_at_9 α).symm
  have h_lhs : delta (cupAW 5 2 b α β) i
             = delta (cupAW 5 2 b (decomp_5_2 α) β) i := by
    apply delta_pointwise_eq; intro j
    exact cupAW_pointwise_eq α (decomp_5_2 α) β β h_α_pw (fun _ => rfl) j
  have h_delta_α_pw : ∀ j, delta α j = delta (decomp_5_2 α) j :=
    fun j => delta_pointwise_eq α (decomp_5_2 α) h_α_pw j
  have h_rhs1 : cupAW 5 3 b (delta α) β (castA b i)
              = cupAW 5 3 b (delta (decomp_5_2 α)) β (castA b i) :=
    cupAW_pointwise_eq (delta α) (delta (decomp_5_2 α)) β β
      h_delta_α_pw (fun _ => rfl) (castA b i)
  have h_rhs2 : cupAW 5 2 (b+1) α (delta β) (castB b i)
              = cupAW 5 2 (b+1) (decomp_5_2 α) (delta β) (castB b i) :=
    cupAW_pointwise_eq α (decomp_5_2 α) (delta β) (delta β)
      h_α_pw (fun _ => rfl) (castB b i)
  rw [h_lhs, h_rhs1, h_rhs2]
  unfold decomp_5_2
  rw [delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      delta_cupAW_add_left, delta_cupAW_add_left, delta_cupAW_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_delta_add_left, cupAW_delta_add_left, cupAW_delta_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left,
      cupAW_add_left, cupAW_add_left, cupAW_add_left,
      h_components ⟨0, by decide⟩, h_components ⟨1, by decide⟩,
      h_components ⟨2, by decide⟩, h_components ⟨3, by decide⟩,
      h_components ⟨4, by decide⟩, h_components ⟨5, by decide⟩,
      h_components ⟨6, by decide⟩, h_components ⟨7, by decide⟩,
      h_components ⟨8, by decide⟩, h_components ⟨9, by decide⟩]
  exact combine_10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ### Concrete corollaries at `b ∈ {1, 2}`

At each concrete `b` the `castA`/`castB` casts reduce to
identity, so `h_components` can be passed without explicit
casts.
-/

/-- α-decomp lens at `(5, 2, 1)`.  Corollary of
    `leibniz_via_α_decomp_general` at `b = 1`. -/
theorem leibniz_via_α_decomp_21
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3))
    (h_components : ∀ p : Fin 10,
      delta (cupAW 5 2 1 (bz5_2 α p) β) i
        = xor (cupAW 5 3 1 (delta (bz5_2 α p)) β i)
              (cupAW 5 2 2 (bz5_2 α p) (delta β) i)) :
    delta (cupAW 5 2 1 α β) i
      = xor (cupAW 5 3 1 (delta α) β i)
            (cupAW 5 2 2 α (delta β) i) :=
  leibniz_via_α_decomp_general α β i h_components

/-- α-decomp lens at `(5, 2, 2)`.  Corollary of
    `leibniz_via_α_decomp_general` at `b = 2`. -/
theorem leibniz_via_α_decomp_22
    (α β : Cochain 5 2) (i : Fin (binom 5 4))
    (h_components : ∀ p : Fin 10,
      delta (cupAW 5 2 2 (bz5_2 α p) β) i
        = xor (cupAW 5 3 2 (delta (bz5_2 α p)) β i)
              (cupAW 5 2 3 (bz5_2 α p) (delta β) i)) :
    delta (cupAW 5 2 2 α β) i
      = xor (cupAW 5 3 2 (delta α) β i)
            (cupAW 5 2 3 α (delta β) i) :=
  leibniz_via_α_decomp_general α β i h_components

end E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLiftAlpha
