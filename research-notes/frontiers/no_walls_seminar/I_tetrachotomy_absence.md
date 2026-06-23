# I — the TETRACHOTOMY: absence `∅` is a fourth status, prior to `0 / 1 / many`

*No-walls seminar, Round 3.  Orchestrator hypothesis I, tested against the corpus and machine-checked.
Anchors grep-verified file:line; the new witness is ∅-axiom (`#print axioms` → "does not depend on any
axioms", scanned from repo root).*

---

## 0. Verdict up front

**TETRACHOTOMY — confirmed and built.**  Absence (`∅`, no fiber / no term) is a **genuine fourth
status, prior to the `0 / 1 / many` section-count trichotomy**.  It does not collapse into the wall.

> The section-count `0 / 1 / many` (wall / forced / free) answers *"how many readings does the fiber
> have?"* — it **presupposes the fiber exists**.  `∅` answers the **prior** question *"is there a
> fiber / term to read at all?"*.  The wall is `¬∃ section` of an **inhabited** self-cover (the
> diagonal bites a term-rich fiber); absence is `¬∃ section` because the fiber is **uninhabited**
> (there is no term to read — the construction has not been made).  Same `¬∃ section`, structurally
> different reason — and the reason is a proven, ∅-axiom predicate on the fiber.

The skeptic's *"absence ≠ obstruction ≠ parameter"* (`C_skeptic_genuine_walls.md` §4 caveat 2) is
exactly `∅ ≠ 0(wall) ≠ many(free)`, and the seminar was right to keep the three separate.  This round
**promotes that prose distinction to a machine-checked `∅ ≠ 0` theorem.**

**∅-axiom witness BUILT:** `lean/E213/Lib/Math/Logic/SectionCountWithAbsence.lean`
(13 pure / 0 dirty; `lake build` clean; `#print axioms` on all headlines → "does not depend on any
axioms").

---

## 1. The four-status table

| status | section-count question | what it is | distinguishing predicate (fiber level) | Lean anchor |
|---|---|---|---|---|
| **`∅` (absence)** | *is there any term in the fiber?* — **NO** | the missing modelling input — ambient `S³`, no `Raw`/`Lens` term | fiber **uninhabited** `¬∃ y, Fib x` | `absence_fiber_uninhabited`, `absence_no_section` |
| **`0` (wall)** | how many total sections? — **none** | the diagonal: inhabited self-cover, no surjection | fiber **inhabited** `∃ y, Fib x`, yet no total section | `wall_fiber_inhabited`, `wall_no_total_section` (= `cantor_general`) |
| **`1` (forced)** | — exactly one | the atomic data `C = (NS,NT,d,c)` | fiber inhabited, `∃!` | `SectionCount.forced_exists_unique` |
| **many (free)** | — ≥ 2 | the Lens parameters σ / base / modulus | fiber inhabited, `≥ 2` | `SectionCount.free_two_sections` |

The decisive separator is the **fiber-inhabitation predicate**, itself ∅-axiom:
`absence_distinct_from_wall` (`SectionCountWithAbsence.lean`) bundles, in one theorem:

  * `absence_no_section`  — `¬∃ section` of `absenceFib`,
  * `absence_fiber_uninhabited` — `¬∃ y, absenceFib.Fib ()` (the fiber is `Empty`),
  * `wall_no_total_section` — `¬∃ f, Surjective f` over `wallFib Nat` (= `cantor_general`),
  * `wall_fiber_inhabited 0` — `∃ y, (wallFib Nat).Fib 0` (the fiber `Nat → Bool` has the constant
    `true`).

So both `∅` and `0` are `¬∃ section`, but `∅`'s fiber is **uninhabited** and `0`'s fiber is
**inhabited** — the proven cut.

---

## 2. Why absence does not collapse into 0 / 1 / many (the rigorous decision, Task 1)

The orchestrator's precise distinction holds under scrutiny:

  * **∅ = the fibration's BASE/fiber is empty/unbuilt** (no construction `C` yet — no term to read).
  * **0 = `C` exists, its self-cover reading has no canonical section** (the diagonal, on an
    *inhabited* fiber).

**Does ∅ collapse into 0 (wall)?  No.**  The wall (`cantor_general`) is a statement *about an
inhabited self-cover*: it takes `f : A → (A → Bool)` — a fiber `A → Bool` that **has terms** — and
proves no such `f` is surjective.  Remove the inhabitant and the diagonal has nothing to act on:
there is no self-cover, no `g x := !(f x x)` to construct, because there is no `f x` to negate.  The
wall is an *obstruction on a built construction*; absence is the *non-existence of the construction*.
`wall_fiber_inhabited` vs `absence_fiber_uninhabited` is the ∅-axiom proof that these are different.

**Does ∅ collapse into 1 (forced)?  No — and this is the subtle near-miss.**  An empty *base* (rather
than empty fiber) would give a *vacuously unique* section (`∀ x ∈ ∅, …` holds trivially) — that
collapses to `1`/forced, the wrong model.  The witness therefore models absence as an **empty fiber
over an *inhabited* base** (`absenceFib : X = Unit, Fib = Empty`): the base point exists (we can
*name* the construction we want — "the ambient `S³`"), but the reading-type carries no inhabitant.
That gives `¬∃ section` (not a vacuous unique one), correctly seating absence apart from forced.

**Does ∅ collapse into many (free)?  No.**  A free σ needs an *inhabited* fiber with ≥ 2 readings to
dial (`freeFib`'s fiber `Bool`).  An empty fiber has zero readings — nothing to dial.  Absence has no
operand, the exact opposite of a free parameter.

**Verdict: absence is genuinely fourth, prior to the trichotomy** — the `0/1/many` count presupposes
the fiber exists; `∅` is the answer when it does not.

---

## 3. The ∅-axiom witness (Task 2)

`lean/E213/Lib/Math/Logic/SectionCountWithAbsence.lean` (imports only `SectionCount`):

  * `StatusCount` — the four-status inductive (`absence | zero | one | many`), `classify4` reads off
    `absence / wall / forced / free`; `ofSectionCount` embeds the trichotomy as the three built-fiber
    tags (no preimage for `absence` — it is *prior* to the count).
  * `absenceFib` — `X := Unit`, `Fib := fun _ => Empty` (empty fiber over an inhabited base).
  * `absence_no_section` — `¬∃ section` (a section at `()` would be an `Empty` term; `(s ()).elim`).
  * `absence_fiber_uninhabited` / `wall_fiber_inhabited` — the `∅ ≠ 0` fiber-level cut.
  * `tetrachotomy_complete` (all four tags + classifier) and `tetrachotomy_distinct` (`absence` is a
    separate pole from wall/forced/free, by `decide`).
  * `absence_distinct_from_wall` — the headline conjunction: absence's `¬∃ section` + uninhabited
    fiber, versus the wall's `¬∃ surjective section` + inhabited fiber.

**Purity:** `lake build` clean; `tools/scan_axioms.py` → **13 pure / 0 dirty**; `#print axioms` on
`absence_no_section`, `absence_distinct_from_wall`, `tetrachotomy_complete`, `tetrachotomy_distinct`
→ all "does not depend on any axioms".  No `propext` / `Classical` / `funext` / `Quot.sound` /
Mathlib.  (`Empty.elim` / `nomatch` and `decide` on closed tags are axiom-free.)

**Honest scope.**  The witness exhibits the *shape* of absence (uninhabited fiber ⟹ no section,
proven distinct from the diagonal).  The *specific* ambient-`S³` absence (`colimit_quotient_synthesis.md`
Side B item 3) stays a **located modelling gap**, not a built `Raw` type — modelling "no term" with the
empty Lean type `Empty` is faithful, but `Empty` is itself a (degenerate) naming whose point is that it
*fails to land a term*, not that 213 owns a privileged exterior object.  The general classifier
`Fibration → StatusCount` (deriving the status from structure, now a *four*-way unification with the
new absence branch) remains the located, undelivered target — same residue `SectionCount.lean`
recorded, one notch deeper.

---

## 4. Absence and the no-exterior axiom (Task 3)

Absence is **categorically different** from wall / forced / free, and §5.4
(`seed/AXIOM/05_no_exterior.md`) licenses it directly:

  * **not a wall** — `cantor_general` needs an *inhabited* self-cover to bite; with no construction
    there is no diagonal to run (no obstruction).
  * **not a free parameter** — a free σ needs an inhabited fiber with ≥ 2 readings; an empty fiber has
    none (no operand to dial — §5.1 *"free parameters have no operand"*, matching the CLAUDE.md
    "fine-tuning as forbidden" correction).
  * **not forced** — a forced atom is a *unique inhabited* reading; absence is *no* reading.

It is the honest **"not yet built / outside the current model"** that §5.4's guard keeps live:
*"If, after genuinely looking, no internal handle is there, say so plainly.  The honest 'not reached
from inside' is the falsifier doing its work."*  Absence is that plain report — the calculus's honest
**"I have no term for this"**.

Crucially this is **not an exterior import** (§5.1).  Naming "no `Raw`/`Lens` term for the ambient
`S³`" is a residue-internal *pointing that fails to land* — by §5.3, *"unsolved = a proof-residue not
yet pointed at, not located in the residue family"*, which is precisely an **empty fiber**.  Absence
is the section-count of an **unbuilt** construction; the trichotomy is the section-count of a **built**
one.  §5.4's stance — *internal-first while keeping "is this really internal?" a live question* — is
exactly the `∅` status: not pre-emptively a wall (no obstruction declared), not reflexively dissolved
(it is honestly recorded as not-yet-landed), but held open.

So the seminar's recurring "third status" is now seated: **absence is the zeroth column of the
classification, the section-count of a fiber that does not (yet) exist.**

---

## 5. The unified picture after Round 3

> **One axiom (§5.1, no exterior dialer) governs a FOUR-status classification of every construction
> `C`'s reading-fibration:**
>
> **`∅` (no fiber — absence, the unbuilt / missing input) `|` `0` (inhabited fiber, no section — the
> one diagonal WALL) `|` `1` (FORCED atom) `|` many (FREE σ).**
>
> The `0 / 1 / many` trichotomy (`SectionCount.lean`) counts the sections of a *built* fiber; `∅`
> (`SectionCountWithAbsence.lean`) is the *prior* status when the fiber is unbuilt.  `∅` is the honest
> §5.4 "no internal handle found"; `0` is the proven, generative diagonal (`one_diagonal_generates`);
> `1`/many are the forced atoms and free Lens parameters (with G's fiber-order law governing the
> symmetry of the free ones).

The "no walls, only free σ" thesis is now fully amended across three rounds: **one wall (the
diagonal, `0`) + free parameters (`1`/many) + located absences (`∅`)** — and all four statuses are
machine-witnessed, ∅-axiom.

---

## 6. Sharpest open question for Round 4

**Is `∅` (absence) the section-count of a fiber, or the section-count of the BASE — and does that
expose a fifth status?**  The witness modelled absence as an *empty fiber over an inhabited base*
(to dodge the vacuous-unique collapse into `1`).  But the ambient-`S³` gap is arguably an **empty
base** ("no index for the construction at all"), which the witness deliberately avoided because an
empty base gives a vacuously-forced `1`.  This asymmetry — *empty fiber ⟹ absence (`∅`)* but *empty
base ⟹ vacuous-forced (`1`)* — suggests the `∅`/`0`/`1`/many axis may itself be **two coupled axes**
(base-existence × fiber-existence × section-count), with the diagonal-table's empty cells either
genuinely empty or hiding a status the seminar has not yet named.  Concretely for R4: **build the
`tagOf : Fibration → StatusCount` master classifier and check whether its case analysis is exhaustive
over (base inhabited?) × (fiber inhabited?) × (section count) — or whether a 2×2×3 grid leaves a cell
no built instance occupies** (the seminar's own residue, one fold up: does the classification of
classifications leave a residue, per `cantor_general` on the space of statuses?).
