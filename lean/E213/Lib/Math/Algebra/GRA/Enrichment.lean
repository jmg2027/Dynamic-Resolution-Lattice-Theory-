import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Hom

/-!
# GRA Enrichment — unified bipartite-carrier enrichment (Phases 11–12)

The marathon's Phases 11–12 enumerated five Readings, each with
a domain-flavoured tagged-Nat type:

  · Walk (R₄)    — `EdgeWalk(length)`    for `K_{3,2}` bipartite walks
  · Cochain (R₁) — `Cochain(degree)`     for cup-product degrees
  · HoTT (R₃)    — `Truncation(level)`   for homotopy n-types
  · Operad (R₂)  — `Operad(level)`       for `E_n` operad levels
  · Analysis (R₅)— `Resolution(exponent)` for resolution shifts

All five carried identical mathematical content modulo cosmetic
renaming.  Now that the shape is known, they collapse to a single
parametric structure `BipartiteCarrier` — a `Nat` tagged with the
(2, 3)-bipartite constraint `n = 0 ∨ n ≥ 2`.  Setting "n = length"
recovers Walk; "n = degree" recovers Cochain; etc.  The domain
flavour was commentary, not structure.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.Enrichment

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Hom

/-! ### §1 — `BipartiteCarrier` — tagged Nat with bipartite constraint -/

/-- A (2, 3)-bipartite enriched carrier: a `Nat` value together
    with the constraint "either trivial (n = 0) or genuine
    (n ≥ 2)".  Excluding `n = 1` reflects `gcd(2, 3) = 1`'s
    exclusion of `1` from `{2a + 3b : a, b ≥ 0}` — the
    K_{3,2}-bipartite walk / cup-product / truncation /
    operad / resolution all carry the same constraint. -/
structure BipartiteCarrier where
  /-- The (2, 3)-arithmetic value (length / degree / level /
      exponent in the five domain readings). -/
  n : Nat
  /-- Constraint: trivial (n = 0) or genuine (n ≥ 2). -/
  constraint : n = 0 ∨ n ≥ 2

/-- The trivial (n = 0) carrier element. -/
def BipartiteCarrier.zero : BipartiteCarrier where
  n := 0
  constraint := Or.inl rfl

/-- The n = 2 carrier element (Walk.two / Cochain.edge2 /
    Truncation.two / Operad.E2 / Resolution.binary). -/
def BipartiteCarrier.two : BipartiteCarrier where
  n := 2
  constraint := Or.inr Nat.le.refl

/-- The n = 3 carrier element. -/
def BipartiteCarrier.three : BipartiteCarrier where
  n := 3
  constraint := Or.inr (Nat.le.step Nat.le.refl)

/-! ### §2 — Combine (additive on `n`); both ⊕ and ⊗ collapse to this -/

/-- Combining two non-trivial bipartite-constrained `Nat` values
    preserves the constraint. -/
private theorem combine_n (a b : Nat)
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

/-- The combine: values add.  In the five domain readings, this
    is concat / cup / suspend / day-convolution / modulus-
    composition — all the same arithmetic. -/
def BipartiteCarrier.combine (x y : BipartiteCarrier) : BipartiteCarrier where
  n := x.n + y.n
  constraint := combine_n x.n y.n x.constraint y.constraint

/-! ### §3 — The enriched (2, 3)-GRA model on `BipartiteCarrier` -/

/-- Grade = the underlying Nat value. -/
def bipartiteGrade : BipartiteCarrier → Nat := BipartiteCarrier.n

/-- Depth = `⌈n/3⌉`, matching all five enrichments + NT. -/
def bipartiteDepth (n : Nat) : Nat := (n + 2) / 3

/-- The unified enriched (2, 3)-GRA model.  Replaces
    `GRA23_EdgeWalk`, `GRA23_CochainEnriched`,
    `GRA23_TruncationEnriched`, `GRA23_OperadEnriched`,
    `GRA23_ResolutionEnriched` — all five were `rfl`-equal in
    structure. -/
def GRA23_Bipartite : GRAModel where
  Carrier := BipartiteCarrier
  grade := bipartiteGrade
  oplus := BipartiteCarrier.combine
  otimes := BipartiteCarrier.combine
  gen1 := 2
  gen2 := 3
  depth := bipartiteDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le.refl
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §4 — Forgetful `GRAHom` to NT -/

/-- Forgetful map: extract the underlying Nat. -/
def forget : BipartiteCarrier → Nat := BipartiteCarrier.n

/-- The forgetful is a `GRAHom` from the enriched model to NT. -/
def forgetHom : GRAHom GRA23_Bipartite NumberTheory.GRA23_NT where
  toFun := forget
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §5 — Reachability and depth at the enriched level -/

/-- Every bipartite carrier of value `n ≥ 2` decomposes as
    `n = 2a + 3b`.  Carrier-level lift of `Common.reach_23`. -/
theorem bipartite_reach (b : BipartiteCarrier) (h : b.n ≥ 2) :
    ∃ a c : Nat, b.n = 2 * a + 3 * c :=
  Common.reach_23 b.n h

/-- The enriched depth on a carrier of value `n` equals `(n + 2) / 3`. -/
theorem bipartite_depth_eq (b : BipartiteCarrier) (_h : b.n ≥ 2) :
    bipartiteDepth b.n = (b.n + 2) / 3 := rfl

end E213.Lib.Math.Algebra.GRA.Enrichment
