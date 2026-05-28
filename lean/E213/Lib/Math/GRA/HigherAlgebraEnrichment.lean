import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom

/-!
# GRA Higher Algebra Enrichment — Phase 12.3 (Operad Reading R₂)

The simplified `GRA23_HigherAlgebra` instance uses `Nat`.  This
file lifts to an `Operad` type carrying the `E_n`-operad level
with the bipartite-operad constraint: `E_0` is the trivial operad,
`E_1` is associative (1-dimensional, below the (2,3)-arithmetic),
and `E_n` for `n ≥ 2` is genuinely homotopical.

An `Operad` is tagged with "level = 0 (E_0, trivial) or level ≥ 2
(`E_n` with `n ≥ 2`, genuinely homotopical)".  This mirrors the
walk/cochain/truncation pattern.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.HigherAlgebraEnrichment

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom

/-! ### §1 — `Operad` type with level constraint -/

/-- An `E_n` operad level with bipartite constraint. -/
structure Operad where
  /-- The operad level (n in `E_n`). -/
  level : Nat
  /-- Level is trivial (E_0) or ≥ 2 (genuinely homotopical). -/
  level_constraint : level = 0 ∨ level ≥ 2

/-- The trivial (E_0) operad. -/
def Operad.trivial : Operad where
  level := 0
  level_constraint := Or.inl rfl

/-- The E_2 (commutative) operad. -/
def Operad.E2 : Operad where
  level := 2
  level_constraint := Or.inr Nat.le.refl

/-- The E_3 (highly commutative) operad. -/
def Operad.E3 : Operad where
  level := 3
  level_constraint := Or.inr (Nat.le.step Nat.le.refl)

/-! ### §2 — Day convolution (⊕) and nested integration (⊗) -/

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

/-- Day convolution (⊕): levels add. -/
def Operad.day (o₁ o₂ : Operad) : Operad where
  level := o₁.level + o₂.level
  level_constraint :=
    combine_level o₁.level o₂.level o₁.level_constraint o₂.level_constraint

/-- Nested integration (⊗): grade-additive composition. -/
def Operad.nest (o₁ o₂ : Operad) : Operad := o₁.day o₂

/-! ### §3 — Enriched (2, 3)-GRA model on `Operad` -/

def operadGrade (o : Operad) : Nat := o.level

def operadDepth (n : Nat) : Nat := (n + 2) / 3

def GRA23_OperadEnriched : GRAModel where
  Carrier := Operad
  grade := operadGrade
  oplus := Operad.day
  otimes := Operad.nest
  gen1 := 2
  gen2 := 3
  depth := operadDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le.refl
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §4 — Forgetful `GRAHom` to NT -/

def forget : Operad → Nat := Operad.level

def forgetHom : GRAHom GRA23_OperadEnriched NumberTheory.GRA23_NT where
  toFun := forget
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §5 — Reachability and depth -/

theorem operad_reach (o : Operad) (ho : o.level ≥ 2) :
    ∃ a b : Nat, o.level = 2 * a + 3 * b :=
  Common.reach_23 o.level ho

theorem operad_depth_eq (o : Operad) (_ho : o.level ≥ 2) :
    operadDepth o.level = (o.level + 2) / 3 := rfl

end E213.Lib.Math.GRA.HigherAlgebraEnrichment
