# Round 1 — synthesis: the section-count trichotomy (0 / 1 / many)

*Integrates agents A (boundaries), B (forcing), C (skeptic), D (classifier) + the orchestrator's
hypotheses H1–H3 (`E_orchestrator_R1_hypothesis.md`).  All four converged; H1–H3 confirmed and sharpened
into a single picture.*

## The resolution of the grand thesis

"The calculus has no walls, only free Lens parameters" is **amended and made precise** (skeptic C carried
the day, but the amendment is *stronger*, not weaker):

> **One axiom (§5.1, no exterior dialer) governs the *section-count* of the reading-fibration over a
> construction `C`, and that count — `0 / 1 / many` — is the complete classification:**
>
> | sections of the reading-fibration | status | what it is | anchor |
> |---|---|---|---|
> | **0** (PROVEN `¬∃` canonical reading) | **the WALL** | the residue's non-surjection = the Lawvere diagonal — *internal & generative* | `object1_not_surjective`, `one_diagonal_generates` (11/0) |
> | **1** (`∃!` canonical) | **FORCED** | the atomic data `C=(NS,NT,d,c)` | `ArityForcing` (arity 2 unique) |
> | **many** (`∃`, none canonical) | **FREE** | the Lens parameters σ / base / modulus / presentation | `ChoiceLens` (12/0), `iProdLens` (8/0) |

So there is **exactly one wall** — the diagonal — and it is **internal** (213's own founding theorem
`distinguishing_always_leaves_residue`) and **generative** (it derives Cantor/Russell/Liar/the residue,
`one_diagonal_generates`).  Everything else classically called a "boundary/axiom" is a **free Lens
parameter** (section-count *many*).  The wall is not a limit *against* 213; it is the `0`-section pole of the
*same* fibration whose `many`-pole is the free parameters and whose `1`-pole is the forced atoms.

**This is the `q=±1` tag one level up** (D's decisive observation, = finding (iii)): section-count
`0 / 1 / many` = `escape / converge-uniquely / run-free`.  The wall is the proven `q=−1` escape (`¬∃`,
reached-by-none); the forced atom is the `q=+1` unique fixed point; the free parameter is the unforced
middle.  The trichotomy IS the residue tag `B` read on the *space of readings*.

## The sharp discriminator (skeptic C)

- **free σ** = a *declined* `Prop` (213 states, never proves) WITH an operand to dial AND per-σ
  computation (`LLPO`, AC, base, resolution).  You can dial it.
- **the wall** = a ∅-axiom *PROVEN* universal negation `¬∃` with NO operand.  You cannot dial a proof to
  "surjective".  *A proof is the structural opposite of a free parameter.*

The pointings (modulus, presentations) are free σ; the residue they approach is reached by **none**
(`object1_not_surjective`).  **The freedom is in the approach; the wall is in the limit.**  The earlier
"refuse it" framing conflated them; the thesis conflated the wall with its free approach-parameters.

## The two kinds of free parameter (A + D), and the two independence axes (H3 confirmed)

The *many*-section pole itself splits (calibrated, not forced):
- **selection-σ** — *closed-fiber* sections (choice, ultrafilter, p-adic base, the binary tag `B`).
  Free **symmetrically**: adjoin σ *or* ¬σ, both consistent.  **= forcing** (B: the σ-glue machinery —
  `familyMeet` 6/0 "the 213-internal counterpart of countable Choice, no external Choice", `iProdLens` 8/0,
  `IsResolutionShift` 17/0 — is ALREADY BUILT; only the *generic* is absent).
- **height-h** — *open-tower* sections (resolution/modulus, presentation, ordinal height).  Free
  **asymmetrically**: always taller, never "less strength" (Gödel II).  **= large cardinals** (A's
  calibrated negative: `DepthHeightDiagonal.height_diagonal_escapes` 43/0 names the *step toward* ε₀, builds
  no ordinal *object* — height is reached-by-none along a *different* axis than selection).

These are **`B`'s two aspects** freely parametrized (D: binary-fiber section IS `B`; modulus IS the
open-tower section = finding (v)) — and they are **the two axes of set-theoretic independence** (forcing /
large cardinals).  A's open point: the symmetric/asymmetric split = the corpus's *proven* escape/converge
asymmetry (`escape_residue_outside` universal-negative vs `converge_residue_fixed` positive-existence) read
on the strength axis.

## Status corrections / honest residue

- **vii′ stands and is sharpened**: LLPO/choice = free selection-σ (symmetric); not a wall.
- **The one genuine wall** = the diagonal (C), internal & generative.  **Novikov–Boone / undecidability**
  is a wall *only by collapsing into the diagonal* (halting = the diagonal instance, `computability_halting.md`);
  no undecidability theorem is yet Lean-formalized (predicted-not-built — open).
- **A third status exists** (C): the ambient-`S³` isotopy quotient is a *missing modelling input* (no
  `Raw`/`Lens` term), neither wall nor forced nor free — **absence ≠ obstruction ≠ parameter** must stay
  distinct.  This is the `S³`-input gap (`colimit_quotient_*`), not a fourth section-count.

## What Round 2 builds (the converged agenda)

1. **`ForcingToy.lean`** (B): the minimal ∅-axiom witness — a 2-point poset, `iProdLens` name, two generics
   `sigmaL/sigmaR`, a σ-dependent global section (`readOp sigmaL 3 = 0 ≠ 3`).  Exhibits "σ free ⟹ both
   models" = the independence toy.  All ingredients already PURE; just the bundling.
2. **The section-count trichotomy as a stated object** (D): is "0 / 1 / many canonical sections" = the
   `q=±1` tag one level up, buildable as a `Moduli(C)` whose tag is `ArityForcing`-uniqueness (forced) vs
   section-multiplicity (free) vs non-surjection (wall)?  This would close the whole picture into one Lean
   statement.
3. **Genericity** (B's question): is "meets every dense set" a *further* free Lens parameter (σ-over-σ,
   the `OnLens` level-two), or the place the no-walls thesis genuinely needs the diagonal?  Decide.
4. **Symmetric-σ vs asymmetric-h** (A's question): prove/locate that the one-way height freedom IS the
   escape/converge asymmetry on the strength axis.
