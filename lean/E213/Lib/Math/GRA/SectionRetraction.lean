import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.NumberTheory
import E213.Lib.Math.GRA.Hom
import E213.Lib.Math.GRA.WalkEnrichment
import E213.Lib.Math.GRA.CochainEnrichment
import E213.Lib.Math.GRA.HoTTEnrichment
import E213.Lib.Math.GRA.HigherAlgebraEnrichment
import E213.Lib.Math.GRA.AnalysisEnrichment

/-!
# GRA Section / Retraction — Phase 14

For each enrichment in Phase 12, the forgetful `GRAHom` from the
enriched carrier to `Nat` has a **section**: a map `Nat → Enriched`
such that `forget ∘ section = id` on the *valid* portion of `Nat`
(values 0 or ≥ 2; values = 1 are unreachable in the (2, 3)
arithmetic because `gcd(2, 3) = 1` excludes only `1` from
representable positives).

This file:
  * defines `Walk.section : ∀ n, n = 0 ∨ n ≥ 2 → EdgeWalk`
  * proves `forget ∘ section = id` (retraction identity)
  * shows the section does **not** preserve `⊕` / `⊗` strictly,
    so it is not a `GRAHom` — but it does preserve grade, and
    so does preserve depth.

Structurally: enriched and simplified Readings form a
**retract pair** — the simplified is a retract of the enriched
under the forget, with the section picking the canonical
enriched representative.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.SectionRetraction

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Hom

/-! ### §1 — Walk section: `Nat → EdgeWalk` for valid values -/

/-- Section: lift a valid Nat (0 or ≥ 2) to a canonical
    `EdgeWalk` of that length. -/
def Walk.section (n : Nat) (h : n = 0 ∨ n ≥ 2) : WalkEnrichment.EdgeWalk where
  length := n
  length_constraint := h

/-- Forget after section is identity on valid values. -/
theorem Walk.forget_section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    WalkEnrichment.forget (Walk.section n h) = n := rfl

/-- The image of the section is exactly the set of valid walks
    (those satisfying the length constraint).  This is the
    "section ∘ forget = id on the image" half of a retraction. -/
theorem Walk.section_forget (w : WalkEnrichment.EdgeWalk) :
    Walk.section w.length w.length_constraint = w := rfl

/-! ### §2 — Cochain / Truncation / Operad / Resolution sections

The same pattern applies to each enrichment.  We give the
sections for completeness and observe the parallel structure.
-/

/-- Section for `Cochain`. -/
def Cochain.section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    CochainEnrichment.Cochain where
  degree := n
  degree_constraint := h

theorem Cochain.forget_section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    CochainEnrichment.forget (Cochain.section n h) = n := rfl

theorem Cochain.section_forget (c : CochainEnrichment.Cochain) :
    Cochain.section c.degree c.degree_constraint = c := rfl

/-- Section for `Truncation`. -/
def Truncation.section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    HoTTEnrichment.Truncation where
  level := n
  level_constraint := h

theorem Truncation.forget_section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    HoTTEnrichment.forget (Truncation.section n h) = n := rfl

theorem Truncation.section_forget (t : HoTTEnrichment.Truncation) :
    Truncation.section t.level t.level_constraint = t := rfl

/-- Section for `Operad`. -/
def Operad.section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    HigherAlgebraEnrichment.Operad where
  level := n
  level_constraint := h

theorem Operad.forget_section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    HigherAlgebraEnrichment.forget (Operad.section n h) = n := rfl

theorem Operad.section_forget (o : HigherAlgebraEnrichment.Operad) :
    Operad.section o.level o.level_constraint = o := rfl

/-- Section for `Resolution`. -/
def Resolution.section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    AnalysisEnrichment.Resolution where
  exponent := n
  exponent_constraint := h

theorem Resolution.forget_section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    AnalysisEnrichment.forget (Resolution.section n h) = n := rfl

theorem Resolution.section_forget (r : AnalysisEnrichment.Resolution) :
    Resolution.section r.exponent r.exponent_constraint = r := rfl

/-! ### §3 — `RetractPair` structure: enriched is a retract of
simplified

A retract pair `(F, S)` between `M_enriched` and `NT` consists of
a forgetful `F : M_enriched → NT` and a section `S : NT_valid →
M_enriched` such that `F ∘ S = id`.  Every enrichment in
Phase 12 forms such a pair.
-/

/-- The retract-pair witness for `WalkEnrichment`. -/
structure WalkRetract where
  /-- Forget. -/
  forget : WalkEnrichment.EdgeWalk → Nat
  /-- Section. -/
  sec : (n : Nat) → (n = 0 ∨ n ≥ 2) → WalkEnrichment.EdgeWalk
  /-- Retraction identity. -/
  retract : ∀ n h, forget (sec n h) = n
  /-- Section identity. -/
  section_id : ∀ w, sec w.length w.length_constraint = w

/-- The retract-pair witness. -/
def walkRetractWitness : WalkRetract where
  forget := WalkEnrichment.forget
  sec := Walk.section
  retract := Walk.forget_section
  section_id := Walk.section_forget

/-! ### §4 — Grade preservation of the section

The section preserves grade trivially (since the section's grade
is `n` and the input is `n`).  This is the data needed to set up
the depth-preservation: the section, while not a `GRAHom` (it
doesn't preserve `⊕` in general because `n = a + b` does not
imply `(n, h_n) = (a, h_a) ⊕ (b, h_b)` at the structure level),
*does* preserve depth.
-/

/-- Section preserves grade for walks. -/
theorem Walk.section_grade (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    WalkEnrichment.GRA23_EdgeWalk.grade (Walk.section n h) = n := rfl

/-- Section preserves depth for walks (when `n ≥ 2`). -/
theorem Walk.section_depth (n : Nat) (h : n = 0 ∨ n ≥ 2) (_hn : n ≥ 2) :
    WalkEnrichment.GRA23_EdgeWalk.depth
      (WalkEnrichment.GRA23_EdgeWalk.grade (Walk.section n h)) =
    NumberTheory.GRA23_NT.depth n := rfl

end E213.Lib.Math.GRA.SectionRetraction
