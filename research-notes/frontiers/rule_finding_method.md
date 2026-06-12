# Finding the rules — a discovery method (the generative half)

`number_tower_theory.md` **states** the rules `R0–R8`, each backed by a Lean
**witness**.  That is the *output*.  This note is the *engine*: the reusable
**method by which such rules are found** — a set of generative moves you put to
any *structure with a generating step* (a tower, an operation hierarchy, a
number system).  The rules are its product; the witnesses are confirmations;
this is the search.

It is the **generative complement** to `theory/meta/boundary_discipline.md`
(which is the *validation* half — the decision procedure that *sorts* candidates
into genuine / forcible).  Find with the moves below; keep with the skeptic.

---

## The engine — eight moves (each is a question; the answer is a candidate rule)

**M1 — Find the generator.**  *"What single construction, iterated, produces
every level?"*  Look for the `iter` / successor / fold underneath.  If found, the
whole structure is one generator's iterations — and that immediately yields the
**recursion-structural (vertical) laws**, which hold at *every* level by the
generator's own induction.  (→ tower: `iter`; `R1`, and the vertical half of
`R2`.)

**M2 — Seek the demotion (the logarithm).**  *"Is there a coordinate in which
this rung becomes the **previous**, simpler one?"*  `log` turns `×` into `+`,
`^` into `×`; the arithmetic version is `vp`.  The demotion is the organizing
map: the whole tower is *one* operation seen at successive demotion-depths.
(→ `R3`.)

**M3 — Watch the *substrate*, not the operation.**  *"When the operation
re-expresses, does the **lattice it lives on** change — its dimension, its
atoms?"*  The operation may be 'the same' (addition) while the **substrate jumps**
(`1`-axis count → `∞`-axis primes).  The substrate's dimension is usually the
*real* invariant, and it is set by **atom-(in)distinguishability** (identical
atoms → one axis; distinguishable atoms → one axis each).  (→ `R4`; the
load-bearing reframe.)

**M4 — Split the laws by direction.**  *"Which laws come from the **generator**
(survive every level) vs the **specific operation** (die at some rung)?"*
Vertical (generator) vs horizontal (algebra: comm/assoc/distrib, which die at
`^`).  Do **not** bundle a horizontal law as if it were structural.  (→ `R2`,
`R5`.)

**M5 — Find the wall, then *do not stop*.**  At `∞`, `0`, non-uniqueness, or
transcendence:
- **`∞` / `0`** → give it a **finite coordinate**; the basis is `0 ≡ ∞` (one
  residue, `06_lens_readings.md` §6.5/§6.9).  The finite coordinate *is* a
  **valuation** (`v(ab)=v(a)+v(b)`, `v(0)=∞`).  (→ `R7`, `R8`.)
- **non-uniqueness** → it is a **gauge** (holonomy), not a failure.  The pattern
  *holds* in the gauge-transformed coordinate; the freedom is the gauge group.
  (→ `R6`.)
- then **seek the gauge-invariant** — the coarse data that survives the gauge
  (for tetration: the growth *rank*, not the value).  (→ `R7`.)

**M6 — Separate canonical from holonomic.**  *"Up to which rung is the
demotion-coordinate **canonical** (unique → flat → closed-form)?  Where does it
become **gauge-dependent** (holonomic)?"*  That boundary is itself a structural
event — the wall.  (→ `R5`/`R6`: canonical through `^`, holonomic at `↑↑`.)

**M7 — Witness or tag.**  Each candidate rule must come with a **∅-axiom
witness** (a concrete Lean instance) *or* an honest tag `[std]` / `[spec]`.  A
claim with neither a witness nor an honest tag is **not yet a rule** — it is a
hope.  (This is what makes the output a theory and not a story.)

**M8 — Run the skeptic (hand off to the validation half).**  Put the candidate
through `boundary_discipline.md`: is it a genuine *shared mechanism*, or a
*forcible map* / *vacuous container* / *resonance*?  Kill the over-claim.  (This
caught `LeveledReadout`, the C4 "type-1 rare" draft, the "↑↑ breaks the pattern"
over-statement, and a phantom citation — every recorded rule survived it.)

**M9 — Iterate; the found rule poses the next question.**  Each rule's wall /
gauge / invariant *is* the next move's input: the demotion (M2) exposes a
substrate (M3); the substrate's wall (M5) exposes a gauge (M6); the gauge exposes
an invariant (M5/M7), which is the next level's object.  The search is a loop,
not a list.

---

## The worked example — the engine producing `R1–R8`

| move | question put to the tower | rule found | witness / tag |
|---|---|---|---|
| M1 | what generates `+,×,^,↑↑`? | `R1` one generator `iter` | `[∅]` `hyperop_succ` |
| M1 | which laws are the generator's? | `R2` vertical (survive) | `[∅]` `hyperop_climb`, … |
| M4 | which are the operation's? | `R2` horizontal (die at `^`) | `[∅]` `pow_not_comm/assoc` |
| M2 | coordinate where `×`→`+`, `^`→`×`? | `R3` log demotes; `vp` = arith log | `[∅]` `vp_mul`, `vp_pow` |
| M3 | does the lattice change? | `R4` dimension `1→∞` (atoms) | `[∅]` `prime_pow_unique`, `ExpVector` |
| M6 | where does completion stop? | `R5` algebraic ≤ `^` / none above | `[∅]` `pow_inverse_splits` `[std]` Abel |
| M5 | non-unique `↑↑` interpolation? | `R6` holonomy = gauge of demotion | `[std]` Abel/super-log |
| M5 | hit `∞`/`0` — finite coordinate? | `R7`/`R8` invariant = valuation; `0≡∞` | `[∅]` `vp_*` `[ax]` §6.5/§6.9 |
| M5 | gauge-invariant of `↑↑`? | `R7` growth **rank** | `[std]` Hardy/surreal |

(Read top-to-bottom: the loop M9 in action — each row's answer is the next
row's question.)

## Why these moves (the principles they encode)

The moves are not arbitrary; they are the **residue/Lens boundary discipline**
turned generative:

- **M1, M2 (generator, demotion)** ≙ *re-derive, don't import*: the residue is
  reached by finding the internal generator / coordinate, never by mapping in an
  external structure (no-exterior).
- **M3 (substrate/dimension)** ≙ *the substrate's degrees of freedom are the
  atoms' distinguishability* — the count-Lens vs the prime-Lens.
- **M5, M6, M8 (∞/0→finite, gauge-not-failure, skeptic)** ≙ *`∞`, `0`, and gauge
  are Lens artifacts, not the thing*: `0 ≡ ∞` (§6.9), presentation-dependence is
  a property of the pointing (`rcut_rescale`), and a forcible unifier is
  over-exteriorization.  Tame them; never mistake the artifact for the residue.

So **finding** a rule = the boundary discipline run *forward* (generate); the
existing decision procedure is the same discipline run *backward* (validate).
Together they are the full loop: **generate with M1–M9, keep with the skeptic,
witness or tag, iterate.**

## Scope

The *method* (M1–M9) is a heuristic, not a theorem — its standing is that it
**actually produced** `R1–R8` with their witnesses (the table above), and that
every rule it produced survived M8.  It is reusable on the next structure (the
open frontiers of `number_tower_theory.md`: a growth-rank valuation; the
Abel-as-holonomic-modulus question; a new tower).  Its *guarantee* is only M7+M8
— a rule is real exactly when it has a witness or an honest tag and survives the
skeptic; the moves M1–M6 are where rules *come from*, M9 is why they keep coming.
