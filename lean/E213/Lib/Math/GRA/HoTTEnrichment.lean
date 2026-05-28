import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom

/-!
# GRA HoTT Enrichment — Phase 12.2 (Truncation Reading R₃)

The simplified `GRA23_HoTT` instance uses `Nat` directly.  This
file lifts to a `Truncation` type carrying the truncation level
with the bipartite-coverage constraint: a non-trivial truncation
needs at least level 2 (the minimum non-discrete homotopy type is
a 2-type; 1-types are essentially sets).

A `Truncation` is tagged with a witness that the level is 0
(contractible, the trivial truncation) or ≥ 2.  This is the
homotopy-type cousin of `EdgeWalk` and `Cochain`.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.HoTTEnrichment

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom

/-! ### §1 — `Truncation` type with level constraint -/

/-- A homotopy n-type recorded by its truncation level.  The
    constraint enforces "level 0 (contractible) or level ≥ 2
    (genuinely n-type)" — the homotopy cousin of the cup-product
    degree-≥-2 constraint. -/
structure Truncation where
  /-- The truncation level. -/
  level : Nat
  /-- Level is trivial or ≥ 2 (genuine n-type). -/
  level_constraint : level = 0 ∨ level ≥ 2

/-- The contractible (level 0) truncation. -/
def Truncation.contractible : Truncation where
  level := 0
  level_constraint := Or.inl rfl

/-- A 2-truncation (set-level). -/
def Truncation.two : Truncation where
  level := 2
  level_constraint := Or.inr Nat.le.refl

/-- A 3-truncation (groupoid-level). -/
def Truncation.three : Truncation where
  level := 3
  level_constraint := Or.inr (Nat.le.step Nat.le.refl)

/-! ### §2 — Suspension (⊕) and smash (⊗) -/

/-- Combining two truncation levels preserves the
    "level 0 ∨ level ≥ 2" constraint. -/
private theorem combine_level (a b : Nat)
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

/-- Suspension `Σⁿ`: levels add. -/
def Truncation.suspend (t₁ t₂ : Truncation) : Truncation where
  level := t₁.level + t₂.level
  level_constraint :=
    combine_level t₁.level t₂.level t₁.level_constraint t₂.level_constraint

/-- Smash product `∧`: levels add (grade-additive composition). -/
def Truncation.smash (t₁ t₂ : Truncation) : Truncation := t₁.suspend t₂

/-! ### §3 — The enriched (2, 3)-GRA model on `Truncation` -/

/-- Grade = truncation level. -/
def truncationGrade (t : Truncation) : Nat := t.level

/-- Depth = ⌈n/3⌉ (minimum truncation compositions). -/
def truncationDepth (n : Nat) : Nat := (n + 2) / 3

/-- The enriched (2, 3)-GRA model on `Truncation`. -/
def GRA23_TruncationEnriched : GRAModel where
  Carrier := Truncation
  grade := truncationGrade
  oplus := Truncation.suspend
  otimes := Truncation.smash
  gen1 := 2
  gen2 := 3
  depth := truncationDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le.refl
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §4 — Forgetful `GRAHom` from `Truncation` to NT -/

/-- Forgetful map: extract the truncation level. -/
def forget : Truncation → Nat := Truncation.level

/-- The forgetful is a `GRAHom`. -/
def forgetHom : GRAHom GRA23_TruncationEnriched NumberTheory.GRA23_NT where
  toFun := forget
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §5 — Reachability and depth -/

/-- Every truncation of level `n ≥ 2` decomposes as `n = 2a + 3b`. -/
theorem truncation_reach (t : Truncation) (ht : t.level ≥ 2) :
    ∃ a b : Nat, t.level = 2 * a + 3 * b :=
  Common.reach_23 t.level ht

/-- The enriched depth equals `(n + 2) / 3`. -/
theorem truncation_depth_eq (t : Truncation) (_ht : t.level ≥ 2) :
    truncationDepth t.level = (t.level + 2) / 3 := rfl

end E213.Lib.Math.GRA.HoTTEnrichment
