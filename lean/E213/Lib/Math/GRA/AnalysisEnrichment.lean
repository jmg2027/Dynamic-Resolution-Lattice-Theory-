import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom

/-!
# GRA Analysis Enrichment — Phase 12.4 (Resolution Reading R₅)

The simplified `GRA23_Analysis` instance uses `Nat`.  This file
lifts to a `Resolution` type carrying the analytic resolution
exponent with the bipartite constraint: a non-trivial resolution
shift has exponent ≥ 2 (the minimum non-discrete cut-shift is the
binary cut at exponent 2 in DRLT, paired with the ternary shift
at exponent 3).

A `Resolution` is tagged with "exponent = 0 (no shift) or exponent
≥ 2 (genuine shift)".

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.AnalysisEnrichment

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom

/-! ### §1 — `Resolution` type with exponent constraint -/

/-- An analytic resolution recorded by its exponent `E`. -/
structure Resolution where
  /-- The resolution exponent. -/
  exponent : Nat
  /-- Exponent is trivial (no shift) or ≥ 2 (real shift). -/
  exponent_constraint : exponent = 0 ∨ exponent ≥ 2

/-- The no-shift resolution. -/
def Resolution.identity : Resolution where
  exponent := 0
  exponent_constraint := Or.inl rfl

/-- Binary cut-double at exponent 2. -/
def Resolution.binary : Resolution where
  exponent := 2
  exponent_constraint := Or.inr Nat.le.refl

/-- Ternary cut-triple at exponent 3. -/
def Resolution.ternary : Resolution where
  exponent := 3
  exponent_constraint := Or.inr (Nat.le.step Nat.le.refl)

/-! ### §2 — Modulus composition (⊕) and polynomial depth (⊗) -/

private theorem combine_exp (a b : Nat)
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

/-- Modulus composition: exponents add. -/
def Resolution.compose (r₁ r₂ : Resolution) : Resolution where
  exponent := r₁.exponent + r₂.exponent
  exponent_constraint :=
    combine_exp r₁.exponent r₂.exponent
      r₁.exponent_constraint r₂.exponent_constraint

/-- Polynomial depth product: grade-additive composition. -/
def Resolution.poly (r₁ r₂ : Resolution) : Resolution := r₁.compose r₂

/-! ### §3 — Enriched (2, 3)-GRA model on `Resolution` -/

def resolutionGrade (r : Resolution) : Nat := r.exponent

def resolutionDepth (n : Nat) : Nat := (n + 2) / 3

def GRA23_ResolutionEnriched : GRAModel where
  Carrier := Resolution
  grade := resolutionGrade
  oplus := Resolution.compose
  otimes := Resolution.poly
  gen1 := 2
  gen2 := 3
  depth := resolutionDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le.refl
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §4 — Forgetful `GRAHom` to NT -/

def forget : Resolution → Nat := Resolution.exponent

def forgetHom : GRAHom GRA23_ResolutionEnriched NumberTheory.GRA23_NT where
  toFun := forget
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §5 — Reachability and depth -/

theorem resolution_reach (r : Resolution) (hr : r.exponent ≥ 2) :
    ∃ a b : Nat, r.exponent = 2 * a + 3 * b :=
  Common.reach_23 r.exponent hr

theorem resolution_depth_eq (r : Resolution) (_hr : r.exponent ≥ 2) :
    resolutionDepth r.exponent = (r.exponent + 2) / 3 := rfl

end E213.Lib.Math.GRA.AnalysisEnrichment
