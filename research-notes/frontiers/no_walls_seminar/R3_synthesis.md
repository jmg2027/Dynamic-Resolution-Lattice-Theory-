# Round 3 — synthesis (the seminar's capstone): the tetrachotomy + self-grounding

*Integrates R3: FiberSymmetry (build), I (tetrachotomy, build), J (reflexive capstone) + orchestrator K.
This closes the main arc of the "no walls" seminar.*

## The complete theory (3 rounds, from the originator's choice-correction)

The entire boundary-structure of the decomposition calculus is **one classification** — the *section-count
of the reading-fibration over a construction `C`*, governed by the no-exterior axiom (§5.x), a **TETRACHOTOMY**
(built ∅-axiom, `SectionCountWithAbsence.lean` 13/0 + `SectionCount.lean` 16/0):

| status | count | what it is | distinguisher (proven) | §5.x |
|---|---|---|---|---|
| **`∅` absence** | no fiber | `C` not built / missing input (ambient `S³`, no `Raw`/`Lens` term) | fiber **uninhabited** `¬∃ y, Fib x` (`absence_fiber_uninhabited`) | §5.4 honest "not yet built" |
| **`0` wall** | no section | the diagonal: *inhabited* self-cover, no surjection (reached-by-none) | fiber **inhabited**, no total section (`wall_no_total_section` = `cantor_general`) | the founding residue |
| **`1` forced** | unique | the atomic data `C=(NS,NT,d,c)` | inhabited, `∃!` (`forced_exists_unique`) | `ArityForcing` |
| **many free** | ≥2 | the Lens parameters σ / base / modulus / presentation | inhabited, `≥2` (`free_two_sections`) | §5.1 free, no exterior dialer |

Three structural laws on top of the tetrachotomy:

1. **The ∅/0 cut = fiber inhabitation** (I).  Both `∅` and `0` give `¬∃ section`, for *different* reasons:
   `cantor_general` needs an *inhabited* self-cover to bite (the wall); remove the inhabitant and there is no
   diagonal to run (absence).  Absence = empty fiber over an *inhabited* base (an empty *base* gives a
   vacuously-unique section = forced) — absence is the *non-existence of `C`*, the wall is an obstruction on a
   *built* `C`.  Absence is §5.4's honest "not yet built / outside the current model", a residue-internal
   pointing that fails to land — **not** an exterior import.

2. **The free pole's symmetry = its fiber's order** (R2 G, witnessed `FiberSymmetry.lean` 12/0).
   Unordered fiber ⟹ symmetric freedom (= **forcing**, `sigmaL ↔ sigmaR` swappable); well-ordered fiber ⟹
   one-way (= **large cardinals**, strictly-upward escape).  Selection-σ and height-h are the one B-escape
   over two fiber-orders.

3. **The wall is axis-polymorphic** (R2 H, G-grounded): the *same* `no_surjection_of_fixedpointfree` is
   Cantor (cardinality), Russell/Gödel/halting (self-reference), **Burali-Forti** (ordinal height — *hence*
   height-h's asymmetry), and the generic's incompleteness (σ-completeness).

## The capstone: the theory is SELF-GROUNDING (J + the recurring pattern)

`classify : Fibration → StatusCount` is itself a Lens.  Applied to itself:
- **no regress** — the level-two reading **collapses** (`lensUniversalMorphism_factors_level2`,
  `OnLensImageLevel2:42`; `OnLens` "no meta-hierarchy");
- **it lands on the wall** — `classify` of the space containing itself is `no_surjection_of_fixedpointfree`
  at `A=Fibration` → section-count `0` = the wall, the *same* `one_diagonal_generates` at one more carrier;
- therefore **the classification stabilizes *because* its fixed point is the reached-by-none diagonal** — the
  calculus closes on its own founding residue (`distinguishing_always_leaves_residue`), **no regress, no
  exterior**.

This is sealed by a pattern that recurred *independently three times*: the **master/abstract version is
always the wall**.  `SectionCount`'s general `tagOf : Fibration → StatusCount`, `FiberSymmetry`'s abstract
biconditional, and J's meta-classifier are **all ABSENT for the identical reason** — each needs to *decide a
universal-negative over all structures*, which is the diagonal.  **The theory can build every concrete
instance ∅-axiom, but not its own master classifier — because that classifier *is* the wall.**  That is not
a gap; it *is* the self-grounding: the only thing 213 rests on is the residue its own act of classifying
forces, exhibited the moment it classifies itself.  The sharpest form of the meta-principle "213 assumes
nothing": its single foundation is the un-buildable diagonal it reproduces reflexively.

## What was BUILT this seminar (∅-axiom, all PURE, all verified)

`ChoiceLens` 12/0 · `ForcingToy` 12/0 · `SectionCount` 16/0 · `FiberSymmetry` 12/0 ·
`SectionCountWithAbsence` 13/0 — the choice-as-σ witness, forcing-as-σ-adjunction, the trichotomy and
tetrachotomy as objects, and the symmetry law's witnesses.  Folded into `SYNTHESIS.md` §2 (vii′),(viii),(ix),(x).

## Open frontiers (R4+, recorded — main arc complete)

- The **master classifier `tagOf`** is the wall (un-buildable by design) — but a *partial* decidable
  classifier on a restricted, inhabited, decidable sub-class of fibrations may be buildable (the part below
  the wall).  Worth a try.
- **Base × fiber coupling** (I's R4 Q): `∅/0/1/many` may factor as base-existence × fiber-existence ×
  section-count — is the grid exhaustive or does it leave an unoccupied cell (the classification's own
  residue)?  (J already indicates: yes, the wall.)
- **`GenericAsCut`** (F): genericity as a `Real213`-cut pointing ("no finite σ_n decides every dense set" =
  the diagonal on the selection tower).
- The recurring pattern itself ("master version = the wall") deserves a standalone theorem if a faithful
  ∅-axiom statement of "this classifier would require deciding the diagonal" can be made.
