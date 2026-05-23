import E213.Lib.Math.Cohomology.Bipartite.Filled4CellExtension
import E213.Lib.Math.Cohomology.Bipartite.FaceCupHigher
import E213.Lib.Math.Cohomology.Bipartite.SteenrodSquaresAtOmega

/-!
# Sq² at the K_{3,2}^{(c=2)} 4-skeleton — chain-level explicit

Companion to `SteenrodSquaresAtOmega.lean` (Sq⁰, Sq¹ at the
2/3-skeleton).  At the 2-skeleton the Steenrod square
`Sq²(ω) := ω ⌣_0 ω` lives in `C⁴` which is empty, so it is
vacuously zero.  At the 4-skeleton (Filled4CellExtension)
`C⁴ = Fin 1 → Bool` is 1-dim, and we can give an explicit
chain-level value via a defensible AW lift of the cup_0 product.

## The AW lift at σ⁴

The pyramid attaching `σ⁴ → [σ³] → [face_0, face_1, face_2]`
gives a natural "outermost-faces" diagonal approximation for the
cup_0 between two face cochains:

      (α ⌣_0 β)(σ⁴) := α(face_0) ∧ β(face_2).

Other AW lifts (e.g. `α(face_0) ⊕ α(face_1) · β(face_1) ⊕ β(face_2)`)
yield equivalent cohomology classes since `H⁴ = 0` at the
4-skeleton.  The outermost-faces choice is the simplest defensible
AW formula.

## Sq²(ω) at the chain level

For `ω = (1, 1, 1)`:

      Sq²(ω)(σ⁴) = ω(face_0) ∧ ω(face_2) = true ∧ true = true.

So Sq²(ω) is the "all-true" 4-cochain at the chain level —
non-trivial as a cochain but TRIVIAL as a cohomology class in
`H⁴ = 0` at the 4-skeleton (the all-true 4-cochain is `δ³` of
the all-true 3-cochain).

## Steenrod ladder at H² ω — full picture at 4-skeleton

| i | Sq^i(ω) value (chain level)  | landing class |
|---|------------------------------|---------------|
| 0 | ω (idempotent under cup_2)    | H² (non-trivial) |
| 1 | δ²(ω) = true at C³ (cup_1)    | H³ (trivial at 4-skel) |
| 2 | true at C⁴ (cup_0 AW lift)    | H⁴ (trivial at 4-skel) |

Max non-trivial Sq^i class at ω at the 4-skeleton: i = 0.
Sq² is non-trivial at the chain level but trivial as a class.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Sq2At4Cell

open E213.Lib.Math.Cohomology.Bipartite.Filled4CellExtension
open E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology (omega_face_vec)

/-! ## §1 — face_cup_0: outermost-faces AW lift at C⁴

For `α, β : Fin 3 → Bool` face cochains, the cup_0 product at
the 4-cell σ⁴ via the outermost-faces diagonal approximation:

      face_cup_0 α β (σ⁴) := α(face_0) ∧ β(face_2). -/

/-- Outermost-faces AW cup_0 at the 4-skeleton: pairs first face
    of α with last face of β. -/
def face_cup_0 (α β : Fin 3 → Bool) : Fin C4_dim_ext → Bool :=
  fun _ => α ⟨0, by decide⟩ && β ⟨2, by decide⟩

/-! ## §2 — face_cup_0 properties -/

/-- face_cup_0 is zero-preserving in the left argument. -/
theorem face_cup_0_zero_left (β : Fin 3 → Bool) (i : Fin C4_dim_ext) :
    face_cup_0 (fun _ => false) β i = false := by
  unfold face_cup_0
  rfl

/-- face_cup_0 is zero-preserving in the right argument. -/
theorem face_cup_0_zero_right (α : Fin 3 → Bool) (i : Fin C4_dim_ext) :
    face_cup_0 α (fun _ => false) i = false := by
  unfold face_cup_0
  cases α ⟨0, by decide⟩ <;> rfl

/-! ## §3 — Sq² at ω -/

/-- Sq² on face cochains at the 4-skeleton: `Sq²(α) := α ⌣_0 α`. -/
def Sq_2 (α : Fin 3 → Bool) : Fin C4_dim_ext → Bool := face_cup_0 α α

/-- ★★★★ `Sq²(ω) = true` on the unique 4-cell.  At the chain
    level the H² → H⁴ Steenrod square is non-trivial. -/
theorem Sq_2_omega_value : ∀ i : Fin C4_dim_ext,
    Sq_2 omega_face_vec i = true := by
  intro i
  unfold Sq_2 face_cup_0 omega_face_vec
  decide

/-! ## §4 — Cohomology-class triviality at H⁴ = 0

At the 4-skeleton, `H⁴ = ker(no δ⁴) / im δ³ = C⁴ / im δ³`.  We
showed in `Filled4CellExtension` that `im δ³ = C⁴` (both Bool
4-cochains are δ³-images, via `δ³` of the false/true 3-cochains
respectively).  Hence `H⁴ = 0` and every 4-cochain — including
`Sq²(ω) = (true)` — is the zero class in `H⁴`. -/

/-- Witness 3-cochain whose δ³-image is the all-true 4-cochain:
    the all-true 3-cochain. -/
def all_true_3cochain : Fin Filled3CellExtension.C3_dim → Bool :=
  fun _ => true

/-- ★★★★ `Sq²(ω) = δ³(all-true 3-cochain)` at the chain level.
    Confirms `[Sq²(ω)] = 0` in `H⁴` at the 4-skeleton. -/
theorem Sq_2_omega_eq_delta3_alltrue :
    ∀ i : Fin C4_dim_ext,
      Sq_2 omega_face_vec i = delta3 all_true_3cochain i := by
  intro i
  unfold Sq_2 face_cup_0 omega_face_vec delta3 all_true_3cochain
  decide

/-! ## §5 — Capstone -/

/-- ★★★★★★★★ **Sq² at K_{3,2}^{(c=2)} 4-skeleton master**.
    STRICT ∅-AXIOM.

    Closes the Steenrod-square ladder at H² ω with explicit
    chain-level values across all i ∈ {0, 1, 2} at progressively
    larger skeletons:

      · Sq⁰(ω) = ω at C² (non-trivial in H²)
      · Sq¹(ω) = δ²(ω) = (true) at C³ (trivial in H³ at 3-skel)
      · Sq²(ω) = (true) at C⁴ via outermost-faces AW lift
        (trivial in H⁴ at 4-skel; Sq²(ω) = δ³(all-true 3-cochain))

    Max non-trivial Sq^i CLASS at ω at the 4-skeleton: i = 0.
    The Sq² chain value is non-trivial but trivializes upon
    descent to H⁴ = 0. -/
theorem sq_2_at_4_cell_master :
    -- Sq² zero-preserving (both args)
    (∀ β : Fin 3 → Bool, ∀ i : Fin C4_dim_ext,
       face_cup_0 (fun _ => false) β i = false)
    ∧ (∀ α : Fin 3 → Bool, ∀ i : Fin C4_dim_ext,
         face_cup_0 α (fun _ => false) i = false)
    -- Sq²(ω) value at C⁴ = true
    ∧ (∀ i : Fin C4_dim_ext, Sq_2 omega_face_vec i = true)
    -- Sq²(ω) is a coboundary: = δ³(all-true)
    ∧ (∀ i : Fin C4_dim_ext,
         Sq_2 omega_face_vec i = delta3 all_true_3cochain i) := by
  refine ⟨face_cup_0_zero_left, face_cup_0_zero_right,
          Sq_2_omega_value, Sq_2_omega_eq_delta3_alltrue⟩

end E213.Lib.Math.Cohomology.Bipartite.Sq2At4Cell
