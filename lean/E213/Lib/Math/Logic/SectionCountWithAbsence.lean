import E213.Lib.Math.Logic.SectionCount

/-!
# The tetrachotomy — `∅ / 0 / 1 / many` = absence / wall / forced / free (∅-axiom)

No-walls seminar, Round 3 (orchestrator hypothesis I; `research-notes/frontiers/no_walls_seminar/`
`I_tetrachotomy_absence.md`).

`SectionCount.lean` built the `0 / 1 / many` (wall / forced / free) trichotomy as a stated
object.  Every count there presupposes the fiber **EXISTS** — `wallFib` reads an *inhabited*
self-cover `A → Bool` and proves *no surjective* section; `forcedFib`/`freeFib` read inhabited
fibers (`Fin 1`, `Bool`) and count their sections.

The seminar kept surfacing a status the trichotomy could not seat: the skeptic's **ambient-`S³`
absence** (`research-notes/frontiers/colimit_quotient_synthesis.md` Side B item 3 — *"there is no
`Raw`/`Lens` term type for the ambient 3-manifold at all (missing modelling input)"*) and the
recurring **"absence ≠ obstruction ≠ parameter"** (`C_skeptic_genuine_walls.md` §4 caveat 2).
That is the **zeroth status `∅`**, *prior* to `0 / 1 / many`:

> The section-count `0 / 1 / many` answers *"how many readings does the fiber have?"* — it
> presupposes there **is** a fiber to read.  `∅` answers the **prior** question *"is there a
> fiber/term to read at all?"* — and the honest answer for the ambient `S³` is **no**.

So the full classification is a **TETRACHOTOMY**:

| status | section-count question | what it is | distinguishing predicate |
|---|---|---|---|
| **`∅` (absence)** | *is there any term in the fiber?* — **NO** | the missing modelling input (ambient `S³`, no `Raw`/`Lens` term) | fiber is **uninhabited** (`¬∃ y, Fib x`) |
| **`0` (wall)** | how many total sections? — **none** | the diagonal: inhabited self-cover, no surjection | fiber **inhabited**, no total section by `cantor_general` |
| **`1` (forced)** | — exactly one | the atomic data `C = (NS,NT,d,c)` | fiber inhabited, `∃!` |
| **many (free)** | — ≥ 2 | the Lens parameters σ | fiber inhabited, `≥ 2` |

**The precise `∅` / `0` cut (the verdict).**  Both `∅` and `0` give `¬∃ Section`, but for
structurally different reasons, and the difference is a **proven, ∅-axiom-decidable predicate on
the fiber**:

  * **`0` (wall)** — the fiber is **inhabited** (`∃ y : Fib x`, e.g. `fun _ => true : A → Bool`),
    yet the *self-cover* reading has no surjective section: a *built construction `C`* whose
    diagonal forbids a canonical reading.  `wallFib`'s fiber has terms; the obstruction is the
    diagonal, **not** emptiness.
  * **`∅` (absence)** — the fiber is **uninhabited** (`¬∃ y : Fib x`): there is **no term to
    read**.  The construction `C` *has not been made* — the base/fiber is empty/unbuilt.  This is
    not an obstruction (nothing forbids a section — there is simply nothing) and not a parameter
    (nothing to dial).  It is the calculus's honest **"I have no term for this"** (§5.4 below).

`absence_fiber_uninhabited` (`∅`: `¬∃ y, fiber`) versus `wall_fiber_inhabited` (`0`: `∃ y,
fiber`) is the ∅-axiom witness that the two `¬∃ Section` are genuinely distinct: **emptiness, not
the diagonal.**

## Connection to §5.4 (no-exterior; `seed/AXIOM/05_no_exterior.md`)

§5.4's guard licenses exactly this fourth status: *"If, after genuinely looking, no internal
handle is there, say so plainly.  The honest 'not reached from inside' is the falsifier doing its
work."*  Absence is that honest report — **categorically different** from wall/forced/free:

  * it is **not a wall** (no obstruction — `cantor_general` needs an inhabited self-cover to bite;
    there is no construction here for any diagonal to act on),
  * it is **not a free parameter** (no operand to dial — a free σ needs an *inhabited* fiber with
    ≥ 2 readings; an empty fiber has none),
  * it is **not forced** (a forced atom is a *unique inhabited* reading; absence is *no* reading).

It is the **"not yet built / outside the current model"** status §5.4 keeps live as a question.
Crucially this is **not** an exterior import (§5.1): naming "no term for the ambient `S³`" is a
residue-internal pointing that *fails to land* — the proof-residue is **not yet located**
(§5.3 *"unsolved = a proof-residue not yet pointed at"*), which is precisely an empty fiber.
Absence is the section-count of an **unbuilt** construction; the trichotomy is the section-count of
a **built** one.

Pure-Lean: `Empty.elim` / `nomatch` on the empty fiber, `decide` on closed tags, the reused
∅-axiom `cantor_general`.  No `propext`, no `Classical`, no `funext`/`Quot.sound`, no Mathlib.
-/

namespace E213.Lib.Math.Logic.SectionCountWithAbsence

open E213.Lib.Math.Logic.SectionCount
  (Fibration Section SectionCount wallFib forcedFib freeFib
   wallTag forcedTag freeTag wall_no_total_section)

/-! ## §1 — the absence tag: extend the trichotomy with the prior status `∅` -/

/-- ★ The **four-status tag** — the tetrachotomy as an explicit object.  `absence` is the *prior*
    status: it answers "is there a fiber/term to read at all?" (no), one question *below* the
    `zero/one/many` "how many sections?".  `zero/one/many` mirror `SectionCount` (wall/forced/free)
    and presuppose an existing fiber. -/
inductive StatusCount where
  | absence  -- no fiber / no term      → ABSENCE (the missing modelling input, ambient `S³`)
  | zero     -- inhabited, no section   → WALL (the proven diagonal)
  | one      -- a unique section        → FORCED (the atomic data)
  | many     -- ≥ 2 sections            → FREE (the Lens parameters)
  deriving DecidableEq, Repr

/-- The four-status classifier: read `absence / wall / forced / free` off a `StatusCount`. -/
def classify4 : StatusCount → String
  | .absence => "absence"
  | .zero    => "wall"
  | .one     => "forced"
  | .many    => "free"

/-- The trichotomy's `SectionCount` embeds into the tetrachotomy as the three *built-fiber* tags;
    `absence` is the one new tag with no `SectionCount` preimage (it is *prior* to the count). -/
def ofSectionCount : SectionCount → StatusCount
  | .zero => .zero
  | .one  => .one
  | .many => .many

/-! ## §2 — the absence instance: an empty fiber over an inhabited base -/

/-- **Absence fibration.**  Over the inhabited base `Unit`, every fiber is `Empty` — there is **no
    term to read**.  This is the ambient-`S³` shape: the base index exists (we can *name* the
    construction we want), but the fiber type carries no inhabitant — no `Raw`/`Lens` term has been
    built for it.  Distinct from `wallFib`, whose fiber `A → Bool` is *inhabited*. -/
def absenceFib : Fibration where
  X := Unit
  Fib := fun _ => Empty

/-- ★★★ **The absence instance has NO section — because the fiber is EMPTY.**  A section
    `∀ x, absenceFib.Fib x` evaluated at `()` would produce an `Empty` term, which does not exist.
    `¬∃ Section`, but for a reason structurally different from the wall: there is *no term to read*,
    not *an inhabited self-cover no surjection covers*.  ∅-axiom (`nomatch` on `Empty`). -/
theorem absence_no_section : ¬ ∃ _s : Section absenceFib, True := by
  rintro ⟨s, _⟩
  exact (s ()).elim

/-- ★★★ **The absence cut: the fiber is UNINHABITED.**  `absenceFib`'s fiber over `()` is `Empty`
    — `¬∃ y, fiber`.  This is the `∅` discriminator: the reading has no term *at all*. -/
theorem absence_fiber_uninhabited : ¬ ∃ _y : absenceFib.Fib (), True := by
  rintro ⟨y, _⟩
  exact y.elim

/-- ★★★ **The wall cut: the fiber is INHABITED.**  `wallFib`'s fiber over any base point is
    `A → Bool` — `∃ y, fiber` (e.g. the constant `true`).  The wall's `¬∃ section` is the diagonal
    obstructing an *inhabited* self-cover, **not** emptiness.  Contrast with
    `absence_fiber_uninhabited`: this is the proven `∅ ≠ 0` separation at the *fiber* level. -/
theorem wall_fiber_inhabited {A : Type} (x : (wallFib A).X) :
    ∃ _y : (wallFib A).Fib x, True :=
  ⟨fun _ => true, trivial⟩

/-- The absence instance's tag is `absence`. -/
def absenceTag : StatusCount := .absence

/-! ## §3 — the unifying object: one tag, one classifier, all four -/

/-- The three trichotomy tags re-expressed as `StatusCount` (via `ofSectionCount`). -/
def wallTag4   : StatusCount := ofSectionCount wallTag
def forcedTag4 : StatusCount := ofSectionCount forcedTag
def freeTag4   : StatusCount := ofSectionCount freeTag

/-- ★★★ **The tetrachotomy, as one stated object.**  Each of the four status poles carries its
    `StatusCount` tag and `classify4` reads off `absence / wall / forced / free` — the trichotomy
    extended by the prior status `∅`.  The tags are *justified* by the instance theorems:
    `absence_no_section` (+ `absence_fiber_uninhabited`) = `∅`, `wall_no_total_section`
    (+ `wall_fiber_inhabited`) = `0`, and the `SectionCount` originals for `1`/`many`. -/
theorem tetrachotomy_complete :
    (absenceTag = StatusCount.absence ∧ classify4 absenceTag = "absence")
    ∧ (wallTag4 = StatusCount.zero  ∧ classify4 wallTag4 = "wall")
    ∧ (forcedTag4 = StatusCount.one ∧ classify4 forcedTag4 = "forced")
    ∧ (freeTag4 = StatusCount.many  ∧ classify4 freeTag4 = "free") :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- ★★★ **The four statuses are all distinct** — the tetrachotomy genuinely *splits* into four,
    with `absence` a separate pole from `wall`, not a degenerate relabel.  With
    `tetrachotomy_complete` this is the complete `∅ / 0 / 1 / many` classification. -/
theorem tetrachotomy_distinct :
    absenceTag ≠ wallTag4 ∧ absenceTag ≠ forcedTag4 ∧ absenceTag ≠ freeTag4
    ∧ wallTag4 ≠ forcedTag4 ∧ forcedTag4 ≠ freeTag4 ∧ wallTag4 ≠ freeTag4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★ **The sharp `∅ ≠ 0` theorem (absence is not the wall).**  Both give `¬∃ Section`, but the
    *fiber-inhabitation* predicate separates them: the absence fiber is **uninhabited**
    (`absence_fiber_uninhabited`) while the wall fiber is **inhabited** (`wall_fiber_inhabited`).
    A genuine fourth status: emptiness (no term to read), not the diagonal (a term-rich self-cover
    no surjection covers).  Packaged as the conjunction the seminar's
    *"absence ≠ obstruction"* claim required. -/
theorem absence_distinct_from_wall :
    -- absence: no section AND the fiber is uninhabited
    (¬ ∃ _s : Section absenceFib, True) ∧ (¬ ∃ _y : absenceFib.Fib (), True)
    -- wall: no surjective section YET the fiber is inhabited
    ∧ (¬ ∃ f : Section (wallFib Nat), Function.Surjective f)
      ∧ (∃ _y : (wallFib Nat).Fib ((0 : Nat) : (wallFib Nat).X), True) :=
  ⟨absence_no_section, absence_fiber_uninhabited, wall_no_total_section,
   wall_fiber_inhabited ((0 : Nat) : (wallFib Nat).X)⟩

/-! ## §4 — honest residue

What is BUILT: the absence status as a genuine fourth pole, ∅-axiom.  `absenceFib` (empty fiber
over an inhabited base) has **no section** (`absence_no_section`) for a reason proven distinct from
the wall: its fiber is **uninhabited** (`absence_fiber_uninhabited`) whereas the wall's fiber is
**inhabited** (`wall_fiber_inhabited`) — `absence_distinct_from_wall` bundles the `∅ ≠ 0` cut.
The four-status tag `StatusCount`, the classifier `classify4`, the embedding `ofSectionCount`, and
`tetrachotomy_complete` / `tetrachotomy_distinct` bundle all four under one object.

What stays ABSENT (the same residue `SectionCount.lean` records, now one notch deeper): a
**general classifier** `Fibration → StatusCount` that *derives* the status from a fibration's
structure — `absence ⟺ ∃ x, ¬∃ y, Fib x` (an uninhabited fiber), `zero ⟺` inhabited-but-no-total-
section, `one ⟺ ∃!`, `many ⟺ ≥ 2` — as one ∅-axiom `decide`-able function.  The four shapes of
evidence (`Empty.elim`, a `¬∃ Surjective`, a subsingleton, a `≠`) would have to be unified without
`propext`/`Classical`/`funext`.  Here the tags are *assigned* per instance and *justified* by the
separate theorems; the master classifier is the located, undelivered target — and is now a
*four*-way unification (the absence branch is the genuinely new obligation).

A finer point, honest about the absence modelling.  `absenceFib` models *"no term in the fiber"*
with an **empty Lean type** (`Empty`).  That is the faithful internal shape of "the ambient `S³`
has no `Raw`/`Lens` term": the fiber is the type of readings, and an *unbuilt* construction has the
**empty** reading-type.  But naming `Empty` is itself a (degenerate) construction — the residue-
internal honesty of §5.4 is that *this naming fails to land a term* (`absence_no_section`), not
that the calculus possesses a privileged "outside" object.  The witness exhibits the **shape** of
absence (uninhabited fiber ⟹ no section, distinct from the diagonal); the *specific* ambient-`S³`
absence stays a located modelling gap, not a built `Raw` type — exactly as §5.4 keeps "is this
really internal?" a live, unterminated question.
-/

end E213.Lib.Math.Logic.SectionCountWithAbsence
