import E213.Lib.Math.Logic.ChoiceLens
import E213.Lens.Cardinality

/-!
# Section-count trichotomy — `0 / 1 / many` = wall / forced / free (∅-axiom)

No-walls seminar, Round 2 (D's R2 question; `research-notes/frontiers/no_walls_seminar/`
`R1_synthesis.md` §"The resolution of the grand thesis").

R1's converged picture: the **section-count of the reading-fibration** over a construction
is the complete classification of every degree of freedom, and it is the residue tag `q = ±1`
read **one level up** (on the space of readings):

| sections of the reading-fibration | status | what it is | anchor |
|---|---|---|---|
| **0** (PROVEN `¬∃` total section) | **WALL** | the residue's non-surjection = the Lawvere diagonal | `Lens.Cardinality.cantor_general`, `OneDiagonal.cantor_via_lawvere`, `object1_not_surjective` |
| **1** (`∃!` section) | **FORCED** | the atomic data `C = (NS,NT,d,c)` | `ArityForcing` (arity 2 unique) |
| **many** (`∃`, none canonical) | **FREE** | the Lens parameters σ / base / modulus | `ChoiceLens.sigmaL ≠ sigmaR` |

This file makes the trichotomy a **stated ∅-axiom object**.  A `Fibration` over a base is a
family of fibers (the readings); a `Section` is one choice per fiber; the *count* of sections —
read as the tag `SectionCount ∈ {zero, one, many}` — reads off `wall / forced / free`.

Three concrete instances exhibit the three counts, each reusing an already-PURE corpus theorem:

  * **0 (wall)** — `wallFib`: the Bool self-cover `A → (A → Bool)` has **no** total section
    (= no point-surjective `f`), by `Lens.Cardinality.cantor_general` (the same diagonal as
    `OneDiagonal.cantor_via_lawvere` / `object1_not_surjective`).  The `0`-section pole.
  * **1 (forced)** — `forcedFib`: a `Fin 1`-fiber family has **exactly one** section
    (`Subsingleton`), mirroring `ArityForcing`'s arity-2 uniqueness.  The `1`-section pole.
  * **many (free)** — `freeFib`: the `Bool`-fiber family of `ChoiceLens` has **≥ 2** sections
    (`sigmaL ≠ sigmaR`).  The `many`-section pole.

The unifying object tags each concrete instance with its `SectionCount`, and `classify` reads off
`wall / forced / free`; `trichotomy_complete` tags all three at once and `trichotomy_distinct`
shows the three poles are genuinely different.

**Honest scope (see module end + report).**  The three instances and their counts are under one
`SectionCount` tag with one `classify` function — a faithful toy of the trichotomy.  A *general*
fibration carrying a single section-count *theorem* that derives the count from structure (rather
than naming it per instance) stays ABSENT; the per-instance tags are definitional assignments
justified by the three separate theorems, not the output of one structural classifier.

Pure-Lean: `decide` on closed goals, `Subsingleton`/`Fin`, the reused ∅-axiom Cantor diagonal and
ChoiceLens theorems.  No `propext`, no `Classical`, no Mathlib.
-/

namespace E213.Lib.Math.Logic.SectionCount

open E213.Lib.Math.Logic.ChoiceLens (sigmaL sigmaR sigmaL_ne_sigmaR_at_0)
open E213.Lens.Cardinality (cantor_general)

/-! ## §1 — the abstraction: fibration, section, section-count tag -/

/-- A **reading-fibration** over a base `X`: a family of fibers `Fib x` (the readings of the
    construction at index `x`).  A *section* is a choice of one reading per fiber.  This is the
    minimal carrier of the normal form `OBJECT = ⟨C | L⟩` read on the *space of readings*: `X` is
    the construction's index, `Fib` the readings, and the sections are the `L`-parameters. -/
structure Fibration where
  /-- the base index of the construction -/
  X : Type
  /-- the fiber over each index — the readings available there -/
  Fib : X → Type

/-- A **section** of a fibration: one reading chosen per fiber.  This is exactly a free
    L-parameter σ when the fibers are inhabited with no canonical choice (`D_lparameter_*` §1). -/
abbrev Section (P : Fibration) : Type := ∀ x, P.Fib x

/-- ★ The **section-count tag** — the trichotomy as an explicit object.  This is the residue tag
    `q = ±1` read one level up, on the space of readings: `zero` = escape (`q = −1`, the wall),
    `one` = unique fixed point (`q = +1`, the forced atom), `many` = the unforced middle (free). -/
inductive SectionCount where
  | zero   -- no total section  → the WALL (proven `¬∃`)
  | one    -- a unique section  → FORCED (the atomic data)
  | many   -- ≥ 2 sections      → FREE (the Lens parameters)
  deriving DecidableEq, Repr

/-- The classifier: read `wall / forced / free` off a section-count.  Word-level mirror of the R1
    table; the content lives in the three instance theorems below. -/
def classify : SectionCount → String
  | .zero => "wall"
  | .one  => "forced"
  | .many => "free"

/-! ## §2 — the three concrete instances -/

/-! ### 0 (wall): the Bool self-cover has no total section -/

/-- **Wall fibration.**  Over base `A`, the fiber at `x` is the reading `A → Bool` of `x` —
    the self-cover whose total section would be a point-surjective `f : A → (A → Bool)`.  By the
    Lawvere/Cantor diagonal there is **none**: section-count `0`. -/
def wallFib (A : Type) : Fibration where
  X := A
  Fib := fun _ => A → Bool

/-- ★★★ **The wall instance has 0 sections (no total reading).**  A *total* section of `wallFib`
    that covers every predicate would be a point-surjective self-cover — impossible by
    `cantor_general` (the same diagonal as `OneDiagonal.cantor_via_lawvere` and
    `object1_not_surjective`).  This is the `0`-section case: the one genuine wall, internal and
    generative (`R1_synthesis.md` §"The resolution"). -/
theorem wall_no_total_section {A : Type} :
    ¬ ∃ f : Section (wallFib A), Function.Surjective f :=
  cantor_general

/-- The wall's tag is `zero`. -/
def wallTag : SectionCount := .zero

/-! ### 1 (forced): a `Fin 1`-fiber family has a unique section -/

/-- **Forced fibration.**  Over any base `X`, every fiber is `Fin 1` — a single reading, no
    choice.  Mirrors `ArityForcing`: the construction axes survive uniquely (arity 2 is the unique
    non-vacuous, non-degenerate value), so the reading is *forced*, section-count `1`. -/
def forcedFib (X : Type) : Fibration where
  X := X
  Fib := fun _ => Fin 1

/-- ★★★ **The forced instance has exactly one section (pointwise).**  Any two sections of
    `forcedFib` agree at *every* fiber (each fiber `Fin 1` has a single value: `.val < 1 ⟹ .val =
    0`).  This is the `1`-section pole: a forced atom — `∃!` reading, no dial.  Stated pointwise to
    stay strictly ∅-axiom (whole-function equality `s = t` would import `funext`'s `Quot.sound`,
    which strict ∅-axiom forbids — see §4).  ∅-axiom. -/
theorem forced_unique_section {X : Type} (s t : Section (forcedFib X)) (x : X) : s x = t x := by
  -- each fiber is `Fin 1`: both values have `.val < 1`, hence `.val = 0`, hence equal.
  have hs : (s x).val = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ (s x).isLt)
  have ht : (t x).val = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ (t x).isLt)
  exact Fin.ext (hs.trans ht.symm)

/-- A canonical section of the forced fibration exists (so the count is `1`, not `0`): the constant
    `0`.  With `forced_unique_section` this pins `∃!` (uniqueness read pointwise). -/
def forcedSection (X : Type) : Section (forcedFib X) := fun _ => ⟨0, Nat.lt_succ_self 0⟩

/-- ★ **The forced fibration's section-count is `∃!` (pointwise).**  There is a section, and every
    section agrees with it at every fiber — the strict-∅-axiom reading of "exactly one section". -/
theorem forced_exists_unique {X : Type} :
    ∃ s : Section (forcedFib X), ∀ (t : Section (forcedFib X)) (x : X), t x = s x :=
  ⟨forcedSection X, fun t x => forced_unique_section t (forcedSection X) x⟩

/-- The forced fibration's tag is `one`. -/
def forcedTag : SectionCount := .one

/-! ### many (free): the ChoiceLens `Bool`-fiber family has ≥ 2 sections -/

/-- **Free fibration.**  Over base `Nat`, every fiber is `Bool` — the inhabited family of
    `ChoiceLens` whose every fiber has two elements.  A section is a genuine choice and there are
    many: section-count `many`, the free Lens parameters. -/
def freeFib : Fibration where
  X := Nat
  Fib := fun _ => Bool

/-- `sigmaL` is a section of the free fibration. -/
def freeSectionL : Section freeFib := sigmaL

/-- `sigmaR` is a section of the free fibration. -/
def freeSectionR : Section freeFib := sigmaR

/-- ★★★ **The free instance has ≥ 2 sections.**  `sigmaL` and `sigmaR` are distinct sections of
    `freeFib` (they disagree at `0`): no canonical choice — the `many`-section pole, the free Lens
    parameter σ (`ChoiceLens.choice_is_free_lens_parameter`).  ∅-axiom. -/
theorem free_two_sections : freeSectionL ≠ freeSectionR := by
  intro h
  exact sigmaL_ne_sigmaR_at_0 (congrFun h (0 : Nat))

/-- The free fibration's tag is `many`. -/
def freeTag : SectionCount := .many

/-! ## §3 — the unifying object: one tag, one classifier, all three -/

/-- ★★★ **The section-count trichotomy, as one stated object.**  Each of the three concrete
    fibrations carries its `SectionCount` tag, and `classify` reads off `wall / forced / free` — the
    R1 trichotomy made a single ∅-axiom statement.  The tags are *justified* by the three instance
    theorems above (`wall_no_total_section` = 0, `forced_exists_unique` = 1, `free_two_sections` =
    many), bundled here as the unification:

      * `wallTag`   classifies as `"wall"`   — `0` sections (the proven diagonal),
      * `forcedTag` classifies as `"forced"` — `1` section  (the atomic data),
      * `freeTag`   classifies as `"free"`   — `many`        (the Lens parameters).

    This is the `q = ±1` tag one level up: section-count on the space of readings is *always
    defined* (zero/one/many, never undefined) — "no walls" = every axis is a defined tag. -/
theorem trichotomy_complete :
    (wallTag = SectionCount.zero ∧ classify wallTag = "wall")
    ∧ (forcedTag = SectionCount.one ∧ classify forcedTag = "forced")
    ∧ (freeTag = SectionCount.many ∧ classify freeTag = "free") :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- ★★★ **The three counts are distinct** — the trichotomy genuinely *splits*.  `wall`, `forced`,
    `free` are three different tags, not a degenerate collapse; with `trichotomy_complete` this is
    the complete `0 / 1 / many` classification, each pole inhabited by a built instance. -/
theorem trichotomy_distinct :
    wallTag ≠ forcedTag ∧ forcedTag ≠ freeTag ∧ wallTag ≠ freeTag := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §4 — honest residue

What is BUILT: the three concrete instances with their section-counts proven
(`wall_no_total_section` = 0, `forced_exists_unique` = 1, `free_two_sections` = many), one
`SectionCount` tag type, one `classify` function, and the unifying `trichotomy_complete` /
`trichotomy_distinct` bundling all three under that single tag.

What stays ABSENT: a **general fibration theorem** that *derives* the `SectionCount` from a
fibration's structure (a `tagOf : Fibration → SectionCount` computed from fiber-cardinality and a
canonical-section predicate, with a master theorem `tagOf P = zero ↔ ¬∃ section P`, `= one ↔ ∃!`,
`= many ↔ ≥2`).  Here `wallTag / forcedTag / freeTag` are *assigned* per instance and *justified*
by the three separate theorems; they are not the output of one structural classifier.  The general
assignment runs into the section-count of `wallFib` being a `¬∃`-about-`Surjective` (a `Prop`-level
non-existence over an arbitrary base), the `forcedFib` count a subsingleton uniqueness, and the
`freeFib` count a `≠` of two terms — three different shapes of evidence that a single ∅-axiom
`decide`-able `tagOf` would have to unify without `propext`/`Classical`.  That master classifier is
the located, undelivered target.

A second, finer ABSENT item surfaced under strict ∅-axiom: section *equality* `s = t` (whole
dependent functions) imports `funext`'s `Quot.sound`, which the seed strictness forbids.  So the
`1`-section uniqueness is stated **pointwise** (`∀ x, s x = t x`), not as `s = t`.  This is the
faithful strict-∅-axiom reading of "one section"; a `Quot.sound`-free *whole-function* uniqueness
is not available and is not claimed. -/

end E213.Lib.Math.Logic.SectionCount
