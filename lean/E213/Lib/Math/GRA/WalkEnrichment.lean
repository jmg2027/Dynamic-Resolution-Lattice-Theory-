import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom

/-!
# GRA Walk Enrichment — Phase 11

The five Reading instances so far use the *simplified* carrier
`Nat` directly.  The full content of the GRA Universality
conjecture requires lifting each Reading's carrier to the actual
domain object — a walk on `K_{3,2}` for R₄, a cochain for R₁,
an `n`-truncated type for R₃, an `E_n`-algebra for R₂, a
resolution shift for R₅.

This file demonstrates the lifting for R₄ (Graph), via an
`EdgeWalk` type whose grade is the walk length.  The forgetful
to the simplified `GRA23_Graph` model is a `GRAHom` (Phase 9),
exhibiting the simplified Reading as a *quotient* of the
enriched Reading.

The same pattern lifts to the other four Readings; the file is
named "WalkEnrichment" because Walk is the most concrete example
to formalise without further infrastructure.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.WalkEnrichment

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom

/-! ### §1 — `EdgeWalk` — walks on `K_{3,2}` by length only

The full Walk type (carrying actual vertex sequences) is built
elsewhere; here we capture only the *length* data, which is all
that the (2, 3)-grade arithmetic cares about.  An `EdgeWalk` is a
tagged Nat where the tag records that the walk obeys the
`K_{3,2}` length constraint: every walk has length `= 0` (trivial)
or `≥ 2` (because the shortest non-trivial walk is the
`NS-NT-NS` 2-step).

The "shortest non-trivial walk = 2 steps" axiom is what allows
the (2, 3) arithmetic to read off K_{3,2} walks; without it, walks
of length 1 (a single edge) would be reachable, contradicting
A4's "every n ≥ 2 representable" via primitives 2 and 3.
-/

/-- An edge-walk on `K_{3,2}` recorded only by its length.  The
    constraint `length = 0 ∨ length ≥ 2` enforces the K_{3,2}
    bipartite reachability rule. -/
structure EdgeWalk where
  /-- The walk's length (number of edges traversed). -/
  length : Nat
  /-- Length is either trivial (0) or ≥ 2 (a real walk uses at
      least one NS→NT step and one NT→NS step). -/
  length_constraint : length = 0 ∨ length ≥ 2

/-- The trivial (single-vertex, no edges) walk. -/
def EdgeWalk.trivial : EdgeWalk where
  length := 0
  length_constraint := Or.inl rfl

/-- A 2-step walk (one NS→NT and one NT→NS). -/
def EdgeWalk.two : EdgeWalk where
  length := 2
  length_constraint := Or.inr (Nat.le.refl)

/-- A 3-step walk (e.g., NS→NT→NS→NT). -/
def EdgeWalk.three : EdgeWalk where
  length := 3
  length_constraint := Or.inr (Nat.le.step Nat.le.refl)

/-! ### §2 — Walk concatenation (⊕) and tensor (⊗) -/

/-- A helper: combining two non-zero walk-length values keeps the
    "≥ 2 or trivial" property.  When both are ≥ 2, the sum is ≥ 2;
    when one is 0, the sum equals the other. -/
private theorem combine_length (a b : Nat)
    (ha : a = 0 ∨ a ≥ 2) (hb : b = 0 ∨ b ≥ 2) :
    a + b = 0 ∨ a + b ≥ 2 := by
  rcases ha with ha0 | ha2
  · rcases hb with hb0 | hb2
    · left; rw [ha0, hb0]
    · right; rw [ha0, Nat.zero_add]; exact hb2
  · rcases hb with hb0 | hb2
    · right; rw [hb0, Nat.add_zero]; exact ha2
    · right
      exact Nat.le_trans ha2 (Nat.le_add_right a b)

/-- Walk concatenation: lengths add. -/
def EdgeWalk.concat (w₁ w₂ : EdgeWalk) : EdgeWalk where
  length := w₁.length + w₂.length
  length_constraint :=
    combine_length w₁.length w₂.length w₁.length_constraint w₂.length_constraint

/-- Walk tensor (grade-additive, like concat — depth composition
    adds grades, not multiplies). -/
def EdgeWalk.tensor (w₁ w₂ : EdgeWalk) : EdgeWalk := w₁.concat w₂

/-! ### §3 — The enriched `(2, 3)`-GRA model on `EdgeWalk` -/

/-- Grade = walk length. -/
def edgeWalkGrade (w : EdgeWalk) : Nat := w.length

/-- Depth = ⌈n/3⌉ on the underlying length. -/
def edgeWalkDepth (n : Nat) : Nat := (n + 2) / 3

/-- The enriched (2, 3)-GRA model on `EdgeWalk`. -/
def GRA23_EdgeWalk : GRAModel where
  Carrier := EdgeWalk
  grade := edgeWalkGrade
  oplus := EdgeWalk.concat
  otimes := EdgeWalk.tensor
  gen1 := 2
  gen2 := 3
  depth := edgeWalkDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le.refl
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §4 — Forgetful `GRAHom` from `EdgeWalk` to the simplified
`GRA23_Graph` (Nat-carrier).

The forgetful `EdgeWalk → Nat` is `length`, and it preserves
grade / ⊕ / ⊗ since each carrier operation is defined to mirror
the underlying Nat operation.  This exhibits the simplified
Reading as the **image** of the enriched Reading under "forget
the walk-structure-witnesses".
-/

/-- Forgetful map `EdgeWalk → Nat`. -/
def forget : EdgeWalk → Nat := EdgeWalk.length

/-- The forgetful is a `GRAHom`. -/
def forgetHom : GRAHom GRA23_EdgeWalk NumberTheory.GRA23_NT where
  toFun := forget
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §5 — Concrete witness: 2 + 3 walks decompose every length ≥ 2

The full strength of Phase 11 — that **every** `EdgeWalk` of
length `n ≥ 2` can be realised as a sequence of 2-step + 3-step
primitives — is the carrier-level lift of `Common.reach_23`.
-/

/-- For every walk `w` with `length ≥ 2`, the length decomposes
    as `2a + 3b` for some `a, b : Nat`. -/
theorem walk_reach (w : EdgeWalk) (hw : w.length ≥ 2) :
    ∃ a b : Nat, w.length = 2 * a + 3 * b :=
  Common.reach_23 w.length hw

/-- The enriched depth on a walk of length `n` equals `(n + 2) / 3`. -/
theorem walk_depth_eq (w : EdgeWalk) (_hw : w.length ≥ 2) :
    edgeWalkDepth w.length = (w.length + 2) / 3 := rfl

end E213.Lib.Math.GRA.WalkEnrichment
