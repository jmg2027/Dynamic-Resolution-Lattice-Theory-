import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom

/-!
# GRA Cochain Enrichment — Phase 12.1 (Cohomology Reading R₁)

The simplified `GRA23_Cohomology` instance uses `Nat` directly as
the carrier.  This file lifts to a `Cochain` type carrying the
cohomological degree with the bipartite-cohomology length
constraint: a non-trivial cup product on `K_{3,2}^{(c=2)}` has
degree ≥ 2 (the minimum non-trivial cup is `edge ∪ edge` with
degree 2; the minimum non-trivial face-product has degree 3).

A `Cochain` is therefore tagged with a witness that its degree is
either trivial (0, the empty cup product) or ≥ 2 (a non-trivial
cup).  This is the cohomological cousin of the `EdgeWalk`
bipartite-walk constraint from `WalkEnrichment.lean`.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.CochainEnrichment

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom

/-! ### §1 — `Cochain` type with degree constraint -/

/-- A cohomological cochain on `K_{3,2}^{(c=2)}` tagged by its
    degree.  The constraint enforces "degree 0 (empty cup) or
    ≥ 2 (non-trivial cup product)" — the cohomology counterpart
    of the K_{3,2} bipartite-walk length constraint. -/
structure Cochain where
  /-- The cohomological degree. -/
  degree : Nat
  /-- Degree is trivial or ≥ 2 (the minimum non-trivial cup
      product has degree 2 = edge ∪ edge). -/
  degree_constraint : degree = 0 ∨ degree ≥ 2

/-- The trivial (empty cup) cochain. -/
def Cochain.empty : Cochain where
  degree := 0
  degree_constraint := Or.inl rfl

/-- A degree-2 cochain (edge cup edge). -/
def Cochain.edge2 : Cochain where
  degree := 2
  degree_constraint := Or.inr Nat.le.refl

/-- A degree-3 cochain (face cup edge). -/
def Cochain.face3 : Cochain where
  degree := 3
  degree_constraint := Or.inr (Nat.le.step Nat.le.refl)

/-! ### §2 — Cup product (⊕) and tensor (⊗) -/

/-- Combining two non-trivial cochain degrees preserves the
    "degree 0 ∨ degree ≥ 2" property. -/
private theorem combine_degree (a b : Nat)
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

/-- Cup product: degrees add. -/
def Cochain.cup (c₁ c₂ : Cochain) : Cochain where
  degree := c₁.degree + c₂.degree
  degree_constraint :=
    combine_degree c₁.degree c₂.degree
      c₁.degree_constraint c₂.degree_constraint

/-- Cochain tensor (grade-additive). -/
def Cochain.tensor (c₁ c₂ : Cochain) : Cochain := c₁.cup c₂

/-! ### §3 — The enriched (2, 3)-GRA model on `Cochain` -/

/-- Grade = cohomological degree. -/
def cochainGrade (c : Cochain) : Nat := c.degree

/-- Depth = ⌈n/3⌉ (cup-length to reach degree n). -/
def cochainDepth (n : Nat) : Nat := (n + 2) / 3

/-- The enriched (2, 3)-GRA model on `Cochain`. -/
def GRA23_CochainEnriched : GRAModel where
  Carrier := Cochain
  grade := cochainGrade
  oplus := Cochain.cup
  otimes := Cochain.tensor
  gen1 := 2
  gen2 := 3
  depth := cochainDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le.refl
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §4 — Forgetful `GRAHom` from `Cochain` to the simplified
`NumberTheory.GRA23_NT`. -/

/-- Forgetful map: extract the degree from a cochain. -/
def forget : Cochain → Nat := Cochain.degree

/-- The forgetful is a `GRAHom`. -/
def forgetHom : GRAHom GRA23_CochainEnriched NumberTheory.GRA23_NT where
  toFun := forget
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §5 — Reachability and depth at the enriched level -/

/-- Every cochain of degree `n ≥ 2` decomposes as `n = 2a + 3b`. -/
theorem cochain_reach (c : Cochain) (hc : c.degree ≥ 2) :
    ∃ a b : Nat, c.degree = 2 * a + 3 * b :=
  Common.reach_23 c.degree hc

/-- The enriched depth on a cochain of degree `n` equals `(n + 2) / 3`. -/
theorem cochain_depth_eq (c : Cochain) (_hc : c.degree ≥ 2) :
    cochainDepth c.degree = (c.degree + 2) / 3 := rfl

end E213.Lib.Math.GRA.CochainEnrichment
