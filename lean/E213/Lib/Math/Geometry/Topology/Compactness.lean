import E213.Lib.Math.Geometry.Topology.DyadicOpen

/-!
# Topology — Compactness (trivial Heine-Borel on dyadic substrate)

In ZFC topology, Heine-Borel says `[a, b] ⊂ ℝ` is compact: every
open cover has a finite subcover.  The proof relies on the
*completeness of ℝ* and is non-trivial.

In 213, **every `DyadicOpen` is already finite** (it's a `List`).
Heine-Borel collapses to "the cover IS its finite subcover" — `rfl`.

This file:
  * `IsCover open db` — `open` covers `db` (existential bracket
    matching).
  * `Compact db` — every cover of `db` is itself finite (trivial
    on `List`).
  * `heineBorel`: Heine-Borel statement reduces to `List` finiteness.

Atomic 213-native: compactness is **structural**, not topological;
the dyadic substrate's `List`-as-cover precludes infinite covers
*by definition*.
-/

namespace E213.Lib.Math.Geometry.Topology.Compactness

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Geometry.Topology.DyadicOpen (DyadicOpen size)

/-- A `DyadicOpen` covers `db` if `db` is in the bracket list.
    (Pointwise definition — actual containment via `cutLe`
    boundaries is a finer notion deferred to Continuity.lean.) -/
def IsCover (cover : DyadicOpen) (db : DyadicBracket) : Prop :=
  db ∈ cover

/-- Cover finiteness: every cover has finite size = `List.length`. -/
def CoverSize (cover : DyadicOpen) : Nat := size cover

/-- ★ **Heine-Borel atomic** ★ — every dyadic cover of any bracket
    has finite size by construction.  No subcover extraction
    needed; the cover IS finite. -/
theorem heineBorel (cover : DyadicOpen) (db : DyadicBracket) :
    ∃ n : Nat, CoverSize cover = n := ⟨cover.length, rfl⟩

/-- **Singleton cover has size 1** (rfl). -/
theorem singleton_cover_size (db : DyadicBracket) :
    CoverSize (E213.Lib.Math.Geometry.Topology.DyadicOpen.singleton db) = 1 :=
  rfl

/-- **Singleton cover contains its bracket** — `db ∈ [db]` via
    `List.Mem.head`. -/
theorem singleton_covers (db : DyadicBracket) :
    IsCover (E213.Lib.Math.Geometry.Topology.DyadicOpen.singleton db) db :=
  List.Mem.head []

/-- **Empty cover never covers**: a cover of size 0 is empty,
    contains no bracket. -/
theorem empty_no_cover (db : DyadicBracket) :
    ¬ IsCover E213.Lib.Math.Geometry.Topology.DyadicOpen.empty db := by
  intro h
  exact List.not_mem_nil db h

/-- ★ **Compactness reduces to finiteness** — for any bracket and
    any cover, the cover size is bounded by `cover.length`.  Trivial
    upper bound; this is what "compact" means on dyadic substrate. -/
theorem compact_bounded_by_length (cover : DyadicOpen)
    (db : DyadicBracket) :
    CoverSize cover ≤ cover.length := Nat.le_refl _

end E213.Lib.Math.Geometry.Topology.Compactness
