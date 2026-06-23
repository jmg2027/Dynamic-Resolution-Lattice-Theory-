import E213.Lib.Math.Logic.SectionCountWithAbsence

/-!
# The partial classifier `tagOf` — the buildable part below the wall (∅-axiom)

No-walls seminar, Round 5 (`research-notes/frontiers/no_walls_seminar/INDEX.md` R5 line:
*"a partial decidable `tagOf` below the wall (the buildable part)"*).

R4 (`MasterClassifierNoGo.lean`) closed the no-go: the **general** master classifier
`tagOf : Fibration → StatusCount` over *every* `Type`-valued fiber family is the wall —
un-buildable ∅-axiom, because deciding the `zero` (wall) branch is deciding the Lawvere
diagonal's universal-negative over all structures
(`MasterClassifierNoGo.master_classifier_is_the_wall`).

This file builds the **part that IS constructible** — `tagOf` restricted to the domain where
section-existence is **DECIDABLE**.  The precise restriction:

> Replace the `Type`-valued fiber family with a **finite list of per-fiber cardinality
> tags** `FiberCard ∈ {empty, point, multi}` — one tag per fiber, encoding how many
> readings that fiber carries (`0 / 1 / ≥2`).  On this domain the section-count of the whole
> family is computed by **structural recursion** over the list, with **no diagonal to
> decide**: a section is a per-fiber choice, so the product is
>
>   * **absence** (`∅`) — some fiber is `empty` (no term to read → no section at all),
>   * **forced** (`1`) — every fiber is `point` (one reading each → one section),
>   * **free** (`many`) — every fiber inhabited and at least one is `multi` (≥2 readings →
>     ≥2 sections).
>
> The `zero` (wall) tag — *inhabited fibers, yet no total section* — **cannot arise** in this
> finite product domain: a finite product of inhabited fibers always carries a section
> (`pick` each fiber's witness).  The wall lives **only** in the `Type`-valued completion
> where a fiber can be an inhabited *self-cover* `A → Bool` whose section the diagonal forbids.

So this `tagOf` is **total and computable on the decidable domain** and returns exactly three
of the four tetrachotomy tags (`absence / forced / free`); the fourth (`wall`) is the
**boundary**: it is the value the classifier would have to return on the un-decidable
self-cover fibers, and that completion is `MasterClassifierNoGo.master_classifier_is_the_wall`.

**This is the precise self-grounding statement:** the classifier IS buildable below the wall
(this file, total + `decide`-correct), and the wall is *exactly* the undecidable completion
(R4).  The decidable domain ends precisely where a fiber stops being a finite cardinality tag
and becomes a `Type`-valued self-cover.

Pure-Lean: `Bool`/`FiberCard` case-analysis (not `Fin` matches — avoids `Quot` leaks),
structural recursion over `List`, `decide` on closed goals.  No `propext`, no `Classical`, no
`funext`/`Quot.sound`, no compiled-kernel evaluation, no Mathlib.
-/

namespace E213.Lib.Math.Logic.TagOfDecidable

open E213.Lib.Math.Logic.SectionCountWithAbsence (StatusCount classify4)

/-! ## §1 — the decidable fiber family: a finite list of per-fiber cardinality tags -/

/-- ★ A **decidable fiber cardinality** — how many readings one fiber carries, recorded as a
    finite tag rather than a `Type`.  This is the restriction that makes the classifier
    buildable: each fiber's section-count is a *decided datum*, not a `Type` whose
    inhabitation a diagonal must settle.

      * `empty` — `0` readings (no term: the `∅` / absence contribution),
      * `point` — `1` reading  (a forced atom: a single choice),
      * `multi` — `≥ 2` readings (a free σ: many choices).

    Stated as a finite inductive with `DecidableEq` so all downstream classification is
    `decide`-able.  Crucially there is **no `selfCover` constructor**: a fiber that is an
    inhabited self-cover (the wall) is *not representable* here — that is the wall boundary
    (§4). -/
inductive FiberCard where
  | empty   -- 0 readings  → absence contribution
  | point   -- 1 reading   → forced contribution
  | multi   -- ≥2 readings → free contribution
  deriving DecidableEq, Repr

/-- A **decidable fiber family**: a finite list of per-fiber cardinality tags.  The list length
    is the number of fibers (the base index `Fin n` enumerated); each entry is that fiber's
    decided reading-count.  A *section* picks one reading per fiber; the *count* of sections is
    the product of the per-fiber counts — computed by `tagOf` below with no diagonal. -/
abbrev DecidableFamily : Type := List FiberCard

/-! ## §2 — the buildable `tagOf`: total, computable, by structural recursion -/

/-- ★★★ **The partial classifier `tagOf` — the buildable part below the wall.**  Total and
    computable on `DecidableFamily` by structural recursion over the list of fiber tags:

      * empty family `[]` — vacuously every fiber is a point, the unique empty section ⟹
        `one` (forced),
      * any `empty` fiber ⟹ `absence` (the whole product has no section — no term to read),
      * else any `multi` fiber ⟹ `many` (free: ≥2 sections),
      * else all `point` ⟹ `one` (forced: exactly one section).

    `absence` dominates (a single empty fiber kills the product), then `many` dominates `one`.
    Returns three of the four tetrachotomy tags; **never `zero`** — the wall does not arise in
    a finite product of decided cardinalities (§4).  No `propext`/`Classical`; pure structural
    recursion + `FiberCard` case-analysis. -/
def tagOf : DecidableFamily → StatusCount
  | [] => .one
  | .empty :: _  => .absence
  | .multi :: _  => .many
  | .point :: rest =>
    match tagOf rest with
    | .absence => .absence   -- a later fiber is empty ⟹ still absence
    | .many    => .many      -- a later fiber is multi ⟹ free
    | _        => .one       -- all remaining points ⟹ forced

/-- The word-level classifier composed with `tagOf`: read `absence / wall / forced / free`
    off a decidable family directly. -/
def classifyOf (fam : DecidableFamily) : String := classify4 (tagOf fam)

/-! ## §3 — correctness on concrete instances, and totality -/

/-- The empty fiber family `[]` — vacuously forced (the unique empty section). -/
theorem tagOf_nil : tagOf [] = StatusCount.one := rfl

/-- ★★★ **An empty-fiber family is `absence`.**  A family containing a `0`-reading fiber has
    **no section** (no term to read there) — the `∅` pole.  `by decide` on a closed term. -/
theorem tagOf_absence : tagOf [FiberCard.empty] = StatusCount.absence := by decide

/-- Absence dominates: an `empty` fiber anywhere kills the product, regardless of the rest. -/
theorem tagOf_absence_mixed :
    tagOf [FiberCard.point, FiberCard.empty, FiberCard.multi] = StatusCount.absence := by decide

/-- ★★★ **A single-reading family is `forced` (`1`).**  Every fiber a `point` ⟹ exactly one
    section — the forced atom.  `by decide`. -/
theorem tagOf_forced : tagOf [FiberCard.point] = StatusCount.one := by decide

/-- All-`point` families of any (concrete) length are forced. -/
theorem tagOf_forced_long :
    tagOf [FiberCard.point, FiberCard.point, FiberCard.point] = StatusCount.one := by decide

/-- ★★★ **A ≥2-reading family is `free` (`many`).**  An inhabited family with a `multi` fiber ⟹
    ≥2 sections — the free Lens parameter σ.  `by decide`. -/
theorem tagOf_free : tagOf [FiberCard.multi] = StatusCount.many := by decide

/-- `many` dominates `one`: inhabited fibers, at least one `multi` ⟹ free. -/
theorem tagOf_free_mixed :
    tagOf [FiberCard.point, FiberCard.multi, FiberCard.point] = StatusCount.many := by decide

/-- The three buildable poles, classified to words on concrete instances. -/
theorem classifyOf_instances :
    classifyOf [FiberCard.empty] = "absence"
    ∧ classifyOf [FiberCard.point] = "forced"
    ∧ classifyOf [FiberCard.multi] = "free" := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★★ **`tagOf` is TOTAL on the decidable domain — and never returns `zero` (the wall).**
    For every decidable family, `tagOf` returns one of exactly three tags: `absence`, `one`, or
    `many`.  It *always* returns a tag (totality, the buildable part) and the wall tag `zero`
    is **never** produced — the wall does not arise in a finite product of decided
    cardinalities.  Proved by structural induction over the list with `FiberCard` /
    `StatusCount` case analysis (no `Fin` match ⟹ no `Quot` leak). -/
theorem tagOf_total (fam : DecidableFamily) :
    tagOf fam = StatusCount.absence
    ∨ tagOf fam = StatusCount.one
    ∨ tagOf fam = StatusCount.many := by
  induction fam with
  | nil => exact Or.inr (Or.inl rfl)
  | cons hd tl ih =>
    cases hd with
    | empty => exact Or.inl rfl
    | multi => exact Or.inr (Or.inr rfl)
    | point =>
      -- `tagOf (point :: tl)` reads the inner `match tagOf tl with ...`
      simp only [tagOf]
      cases htl : tagOf tl with
      | absence => exact Or.inl rfl
      | zero =>
        -- excluded by `ih`: `tagOf tl` is never `zero`
        rcases ih with h | h | h <;> rw [htl] at h <;> exact absurd h (by decide)
      | one  => exact Or.inr (Or.inl rfl)
      | many => exact Or.inr (Or.inr rfl)

/-- ★★★ **`tagOf` never returns the wall tag `zero`** (the sharp boundary statement).  On the
    entire decidable domain the wall is *unreachable* — corollary of `tagOf_total`.  The wall
    tag is exactly the value reserved for the un-decidable self-cover fibers this domain
    excludes; see §4 and `MasterClassifierNoGo.master_classifier_is_the_wall`. -/
theorem tagOf_never_wall (fam : DecidableFamily) : tagOf fam ≠ StatusCount.zero := by
  rcases tagOf_total fam with h | h | h <;> rw [h] <;> decide

/-! ## §4 — the wall boundary (honest residue)

**Where the decidable domain ends — the precise wall boundary.**

What is BUILT (∅-axiom, this file): `tagOf : DecidableFamily → StatusCount`, **total and
computable** (`tagOf_total`) on the domain where each fiber's reading-count is a *decided* tag
`FiberCard ∈ {empty, point, multi}`.  It returns the correct tetrachotomy tag on every
concrete instance — `absence` for an empty fiber (`tagOf_absence`), `forced` for all-`point`
(`tagOf_forced`), `free` for a `multi` fiber (`tagOf_free`) — by `decide`/structural
recursion, with no `Classical`/`propext`/`funext`.  This is the **classifier below the wall**.

**The wall boundary, stated precisely.**  `tagOf` returns exactly three of the four
tetrachotomy tags and **never `zero`** (`tagOf_never_wall`).  The missing tag `zero` (wall —
*inhabited fibers, yet no total section*) is the boundary:

  * In this finite domain a fiber is a *decided cardinality*.  A finite product of
    **inhabited** fibers (`point`/`multi`, no `empty`) **always carries a section** — pick each
    fiber's witness — so the `zero` case (inhabited, no section) is **structurally impossible**.
    That is *why* the classifier is total and `decide`-able here: there is **no diagonal to
    decide**.
  * The `zero` (wall) tag arises **only** in the `Type`-valued completion, where a fiber may be
    an inhabited *self-cover* `A → (A → Bool)` (`SectionCount.wallFib`) whose total section the
    Lawvere diagonal forbids (`SectionCount.wall_no_total_section`).  Deciding that branch is
    deciding the universal-negative over all structures — the un-buildable completion, closed
    as **`MasterClassifierNoGo.master_classifier_is_the_wall`** (R4):
    a master classifier that decides the diagonal AND is a row of its own cover is a
    `not`-fixed-point, impossible ∅-axiom.

So the decidable domain ends **exactly at the `FiberCard → Type` step**: as long as a fiber is
a finite cardinality tag, `tagOf` is total + computable (`absence/forced/free`); the moment a
fiber becomes an inhabited `Type`-valued self-cover, the section-count question becomes the
diagonal and `tagOf` hits the wall.  This realizes the seminar's R5 frontier:
**the classifier IS buildable below the wall; the wall is exactly the undecidable completion.**
-/

end E213.Lib.Math.Logic.TagOfDecidable
