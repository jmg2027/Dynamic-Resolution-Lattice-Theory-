import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Hom
import E213.Lib.Math.Algebra.GRA.Enrichment

/-!
# GRA Section / Retraction — Phase 14 (post-consolidation)

The (unified) bipartite enrichment's forgetful `GRAHom`
`BipartiteCarrier → Nat` has a **section**: a map `Nat →
BipartiteCarrier` such that `forget ∘ section = id` on the
*valid* portion of `Nat` (values 0 or ≥ 2; value 1 is unreachable
in the (2, 3) arithmetic because `gcd(2, 3) = 1` excludes only
`1` from representable positives).

This file:
  * defines `Bipartite.section : ∀ n, n = 0 ∨ n ≥ 2 → BipartiteCarrier`
  * proves `forget ∘ section = id` (retraction identity)
  * shows the section preserves grade (hence depth) but is not
    a `GRAHom` (does not preserve `⊕` / `⊗` strictly)

Structurally: enriched and simplified Readings form a
**retract pair** — the simplified is a retract of the enriched
under the forget, with the section picking the canonical
enriched representative.

After consolidation, the former five sections (`Walk.section`,
`Cochain.section`, ...) collapse to a single `Bipartite.section`
covering all readings.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.SectionRetraction

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Hom
open E213.Lib.Math.Algebra.GRA.Enrichment
  (BipartiteCarrier GRA23_Bipartite forget)

/-! ### §1 — Section: `Nat → BipartiteCarrier` for valid values -/

/-- Section: lift a valid Nat (0 or ≥ 2) to a canonical
    `BipartiteCarrier`.  Replaces the former five sections
    (`Walk.section`, `Cochain.section`, ...). -/
def Bipartite.section (n : Nat) (h : n = 0 ∨ n ≥ 2) : BipartiteCarrier where
  n := n
  constraint := h

/-- Forget after section is identity on valid values. -/
theorem Bipartite.forget_section (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    forget (Bipartite.section n h) = n := rfl

/-- Section after forget is identity on the enriched carrier.
    "section ∘ forget = id on the image" half of a retraction. -/
theorem Bipartite.section_forget (b : BipartiteCarrier) :
    Bipartite.section b.n b.constraint = b := rfl

/-! ### §2 — `RetractPair` structure

A retract pair `(F, S)` between `BipartiteCarrier` and `Nat`
consists of a forgetful `F : BipartiteCarrier → Nat` and a
section `S : Nat_valid → BipartiteCarrier` such that `F ∘ S = id`.
-/

/-- The retract-pair witness. -/
structure BipartiteRetract where
  /-- Forget. -/
  forget : BipartiteCarrier → Nat
  /-- Section. -/
  sec : (n : Nat) → (n = 0 ∨ n ≥ 2) → BipartiteCarrier
  /-- Retraction identity. -/
  retract : ∀ n h, forget (sec n h) = n
  /-- Section identity. -/
  section_id : ∀ b, sec b.n b.constraint = b

/-- The canonical retract-pair witness. -/
def bipartiteRetractWitness : BipartiteRetract where
  forget := forget
  sec := Bipartite.section
  retract := Bipartite.forget_section
  section_id := Bipartite.section_forget

/-! ### §3 — Grade and depth preservation of the section

The section preserves grade trivially (its grade is `n` and the
input is `n`).  It is not a `GRAHom` (does not preserve `⊕` in
general because `n = a + b` does not imply
`(n, h_n) = (a, h_a) ⊕ (b, h_b)` at the structure level), but it
*does* preserve depth.
-/

/-- Section preserves grade. -/
theorem Bipartite.section_grade (n : Nat) (h : n = 0 ∨ n ≥ 2) :
    GRA23_Bipartite.grade (Bipartite.section n h) = n := rfl

/-- Section preserves depth (when `n ≥ 2`). -/
theorem Bipartite.section_depth (n : Nat) (h : n = 0 ∨ n ≥ 2) (_hn : n ≥ 2) :
    GRA23_Bipartite.depth (GRA23_Bipartite.grade (Bipartite.section n h)) =
    NumberTheory.GRA23_NT.depth n := rfl

end E213.Lib.Math.Algebra.GRA.SectionRetraction
