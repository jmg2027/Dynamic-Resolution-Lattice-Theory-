# Agent D — the free L-parameter: definition, classification, and the forced(C)/free(L) line

*No-walls seminar, Round 1.  Role: classifier/unifier.  Thesis under test: "the
calculus has no walls, only free Lens parameters σ."  This memo asks whether the
several accumulated free parameters (choice σ, p-adic base, resolution/modulus,
presentation, the unforced ±1 tag B) are **one structure**, and where the real
dividing line is.  All Lean names below were grep-verified in `lean/E213/`;
purity claims are from `tools/scan_axioms.py` run this session (probe-file
tooling noise aside, 0 DIRTY on the scanned anchors).*

---

## 0. The one-sentence answer

> A **free L-parameter** is a **section of a fibration of readings over one
> Construction `C`** — a choice of one Lens out of an inhabited family of Lenses
> all sharing the same `C` — for which **no exterior dialer fixes the choice**
> (`05_no_exterior.md` §5.1).  Choice σ, p-adic base, resolution/modulus,
> presentation, and the unforced tag B are **the same structure at different
> fiber-types**; they differ only in *what the fiber is*.  The forced data — the
> Construction axes `C = (NS, NT, d, c)` — are exactly the parameters that are
> **NOT free sections**: they are pinned by `ArityForcing` (a *theorem*, not a
> dial).  The forced/free line is the real structure; "no walls" is the
> statement that everything not pinned by `ArityForcing` is a free section, hence
> dialable, hence not a wall.

---

## 1. Precise definition of a "free L-parameter"

The normal form (`SYNTHESIS.md` §1) is `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`.  Fix a
Construction `C`.  The readings of `C` are not a single `L` but a **family**
`{L_x}_{x ∈ X}`, all faithful-where-they-succeed, all on the *same* `C`.

**Definition (free L-parameter).**  Let `C` be a Construction and let
`π : 𝓛(C) → X` be a fibration whose fibers `π⁻¹(x)` are the readings of `C` that
agree on everything except a coordinate `x`.  A **free L-parameter** is a
*section* `σ : X → 𝓛(C)` of `π` (a rule selecting one reading per index)
satisfying both:

1. **Inhabited fiber / per-σ constructivity.**  Each fiber is inhabited by
   *explicit data* — σ is a rule, not an existence claim.  Applying σ is an
   **act** (`CLAUDE.md`: "Lens application IS a residue self-pointing event"),
   so it is ∅-axiom on a concrete `C` (no AC).  Witness:
   `Lib/Math/Logic/ChoiceLens.lean:51 sigmaL`, `:55 sigmaR` — two explicit total
   sections of `F i := Bool`, scanned PURE.
2. **No exterior dialer (the freedom).**  There is no `C`-internal forcing that
   makes one section canonical (`05_no_exterior.md` §5.1: no exterior position ⟹
   no forced parameter value).  Formally the σ-dependence is *observable*: the
   operation reads differently under different sections —
   `ChoiceLens.lean:71 readOp_sigma_dependent` (`readOp sigmaL 3 ≠ readOp sigmaR 3`),
   bundled with section-distinctness in `:81 choice_is_free_lens_parameter`.
   Both σ's are total readings; **neither is forced** — that *is* the freedom.

So: **free L-parameter = a section of a reading-fibration with inhabited fibers
and no canonical section.**  The "no walls" thesis reads: the apparent wall
("can't take this completion / can't decide this / can't reach this limit") is
the absence of a *canonical* section being mistaken for the absence of *any*
section — but sections exist (computably, per-σ); only canonicity fails.

**The residue is σ-indexed.**  `Residue(L_σ, C)` is parametrized by σ
(`axiom_of_choice.md` "Residue ⊕ — the σ-dependence").  This matters in §4: the
moduli-of-readings has its own residue, the *non-existence of a canonical
section*.

---

## 2. The classification — five instances, one structure

Each known instance is a section of a reading-fibration over the **same** `C`.
What varies is the fiber-type `X` (what is being sectioned).  Verified anchors in
the right column.

| Instance | `C` (shared) | Fiber-type `X` (what σ selects) | Section σ | Lean anchor (grep-verified) |
|---|---|---|---|---|
| **choice σ** | an inhabited family `i ↦ X i` | one distinguishable **per fiber** | a choice function `∀ i, X i` | `ChoiceLens.lean:51,55,71,81` (PURE) |
| **p-adic base** | approximant-sequence-with-modulus | which **valuation** measures "adjacent" (`|·|` vs `p^{−vp}`) | a faithful modulus-reading of ℚ | `CauchyComplete.lean:38`; `Padic/Foundation.lean:41`; `Padic/Norm.lean:335 valEq_add_of_lt`; `PrimeValuation.lean:96 vp_mul` |
| **resolution / modulus** | a refinement tower | which **stage/rate** the reading settles at (`Δ` vs `h→0`; page `r`) | a stage-section of the tower | `Analysis/ResolutionShift.lean:130 IsResolutionShift_compose`; `Geometry/Topology/Continuity.lean:64 compose_modulus_eq` |
| **presentation** | a real-as-pointing | which **approximant sequence** points at the same cut | a presentation of the cut | `Real213/PresentationDependence.lean:56 rcut_rescale`, `:110 crossDetSmall_is_presentation_dependent` (real is presentation-invariant; the *pointing* is not) |
| **unforced tag B** | a **binary** fiber `{left,right}` | the ±1 swap bit, when nothing fixes it | a section of a 2-element fiber = `B` | `ChoiceLens.lean` even/odd σ; `Foundations/ResidueTag.lean multiplier_unimodular` |

### 2.1 Why these are ONE structure (not five)

Three structural facts, each load-bearing:

**(a) Same `⟨C|L⟩` skeleton, different fiber-type.**  base and presentation and
resolution are literally the *same* `C` (approximant-sequence-with-modulus,
`padic.md` "Construction C — one thing"): ℝ and ℚ_p differ in **one slot of the
reading**, not in `C`.  `padic.md`'s own table already nests `base` and `scaling`
*inside* the resolution parameter — i.e. the calculus had begun the
unification before this memo.  The section-of-a-fibration framing makes it
precise: base = section of the *completion*-fibration, resolution = section of
the *resolution-tower* fibration, presentation = section of the
*pointings-over-one-cut* fibration, choice = section of the
*inhabited-family* fibration.  Each is `σ : X → 𝓛(C)`; only `X` differs.

**(b) The binary fiber collapses B into the family.**  Over a 2-element fiber a
section *is* the ±1 tag (`axiom_of_choice.md` "binary choice = B"): `σ ∈
{left,right} = {even,odd} = q=±1`.  So finding (vii′) is not a sixth thing — B is
the **fiber = 2** specialization of the choice σ.  This is the sharpest single
collapse: the residue tag B (Invariant B of `SYNTHESIS.md`) and the free
L-parameter σ are the *same object* read at fiber-cardinality 2.

**(c) The modulus is the `q=+1`-reached-by-none signature, i.e. a section that
never closes.**  `SYNTHESIS.md` finding (v) already proved the modulus is **not a
third invariant** — it is "how a reached-by-none residue is made computable."  In
section language: the resolution/modulus σ is a section of a tower *whose limit
fiber is empty* (reached by none, `object1_not_surjective`).  The section is the
computable narrowing interval; the missing limit is the residue.  So the modulus
is a free L-parameter **of a special kind**: a section into a tower with no top
fiber.  This unifies it with the others (still a section) while keeping the
honest distinction finding (v) drew.

### 2.2 A finer reading: two sub-classes of free L-parameter

The five do split cleanly into **two sub-classes**, by *whether the fibration has
a limit fiber*:

- **Closed-fiber sections (genuine choice).**  choice σ, base, the unforced tag
  B.  The fibers are inhabited *and* the index set is given; the freedom is
  purely "which section."  These align with the LLPO/choice face of B
  (`SYNTHESIS.md` (vii′)): a free parameter admits *both* adjunctions, predicting
  AC's independence (forcing = adjoining a generic section).
- **Open-tower sections (resolution/presentation).**  resolution/modulus,
  presentation.  Here the section is a *cofinal narrowing* and the limit fiber is
  empty (reached-by-none).  The freedom is "which approximant rate/sequence," and
  the residue is presentation-invariant (`rcut_rescale`) while the pointing is
  not (`crossDetSmall_is_presentation_dependent`).

This two-sub-class split is itself the `×↦·` / `×↦+` shadow one level up — the
**discrete-given-index vs cofinal-tower** distinction, the same shape as
`SYNTHESIS.md` finding (vi)'s cyclic-vs-free grading.  I flag it as a *calibrated
distinction, not a forced merge*: both are sections, but the limit-fiber's
(in)habitation is a real invariant of the fibration.

---

## 3. The forced(C) vs free(L-param) dividing line — the real structure

This is the crux the prompt asks to sharpen.  **Not everything is a free σ.**
The Construction axes `C = (NS, NT, d, c)` are **forced** — pinned by a theorem,
not selected by a dialer.

**The forcing is a theorem.**  `Theory/Atomicity/ArityForcing.lean` proves the
relation arity `k=2` is the *unique* non-degenerate, non-vacuous choice over a
`Fin 2` base:
- `:41 reachable3_only_object` — with a 2-element base, every arity-3 reachable
  term is a bare object (the step rule **never fires**: 3 pairwise-distinct args,
  only 2 distinct elements exist — pigeonhole);
- `:66 no_reachable_rel3` — no arity-3 relation term is ever reachable
  (vacuous);
- the general version `Lib/Math/Foundations/ArityForcingGeneral.lean:79
  reachable_base_only` (`N < k ⟹ base-only`), `:91` summary: `(arity k, base
  Fin N)` non-vacuous **iff** `N ≥ k`; combined with arity ≥ 2 (non-degenerate)
  and `N` minimal, `(k,N)=(2,2)` is forced.
Scanned this session: **0 DIRTY**.

**The dividing line, stated precisely:**

| | **Forced data `C`** | **Free L-parameter (section σ)** |
|---|---|---|
| What | `NS, NT, d, c` (the atomic construction axes) | choice / base / resolution / presentation / tag-B |
| Status | pinned by `ArityForcing` *theorem* | unpinned; no canonical section (`05 §5.1`) |
| Dial? | **no exterior dialer exists** — and here that's a *theorem* (the value is forced) | **no exterior dialer exists** — and here that means *free* (no value is forced) |
| Residue | none at the `C` level (the axes ARE the construction) | σ-indexed `Residue(L_σ,C)`; for open-tower σ, reached-by-none |
| Lean | `ArityForcing.lean`, `ArityForcingGeneral.lean` | `ChoiceLens.lean`, `PresentationDependence.lean`, `ResolutionShift.lean`, padic cluster |

**The deep symmetry — and why it is NOT a contradiction.**  Both `C` and `L`
obey "no exterior dialer" (§5.1).  The *same* axiom yields opposite outcomes:
- on `C`: no dialer + the construction must be non-vacuous/non-degenerate ⟹ the
  value is **forced** (only one option survives `ArityForcing`);
- on `L`: no dialer + multiple inhabited sections ⟹ the value is **free** (no
  option is canonical).
So "forced" and "free" are the **two outcomes of one axiom (no exterior dialer)**,
selected by *whether the fibration has a unique surviving section*.  `C` is the
fibration with a **unique** section (forced); `L` is the fibration with **many**
(free).  This is the cleanest statement of the forced/free dichotomy: it is not
two principles but one principle (`§5.1`) read on two fibrations of different
fiber-multiplicity.

**Consequence for the "no walls" thesis.**  A wall would be an axis that is
*neither* forced (no theorem pins it) *nor* a free section (no inhabited fiber to
section).  The thesis claims no such axis exists: every degree of freedom is
either pinned by `ArityForcing` (forced `C`) or is a section of an inhabited
reading-fibration (free `L`).  The honest residual (below) is exactly the place
to test this.

---

## 4. Is the moduli-of-readings itself a 213 object?

**Partially — and instructively so.**

The space of free L-parameters over a fixed `C` is `Sect(π) = {σ : X → 𝓛(C)}`,
the sections of the reading-fibration.  Three observations:

**(a) It IS a 213 object on the closed-fiber side, and it is BUILT.**  The
**meet of a Lens-family** is the inverse-limit object `iProdLens`
(`Lens/Lattice/IndexedJoin.lean:97 iProdLens`, with the universal property
`:82 iJoinLens_is_least` / pointwise view `:106 iProdLens_view`).  A *section* of
the family is a point of the indexed product; the family itself is a 213 object
(a `ι → (α : Type) × Lens α`).  So the *carrier* of the moduli — the family of
readings and its meet — is a genuine ∅-axiom 213 object.  The carrier-polymorphic
difference-Lens (`PairCompletionUniversal.lean
invert_is_the_universal_group_completion`) is the same move on the `L₋` axis: one
theorem, many carriers = a *parametrized* reading object.

**(b) It has its own `⟨C|L⟩ ⊕ Residue`.**  Reading the moduli through a Lens
"pick the section" gives `⟨Sect(π) | eval_x⟩`.  Its residue is **the
non-existence of a canonical section** — which on the closed-fiber side is exactly
the LLPO/choice point (`SYNTHESIS.md` (vii′), `Omniscience.LPO/LLPO`), and on the
open-tower side is the reached-by-none limit (`object1_not_surjective`,
`PresentationDependence`).  So **yes, the moduli-of-readings carries the normal
form one level up**, and its residue is precisely the free parameter's
un-canonicalizability.  This is the reflexive turn the corpus already runs
(`SYNTHESIS.md` §6): the calculus describes its own apparatus, and here the
apparatus is *the space of dials*.

**(c) The honest gap — no NAMED `Moduli(C)` / `Completion(base)` object.**  As
with the rest of the corpus, the *engine* is built (`iProdLens`,
`PairCompletionUniversal`, `ResolutionShift`, `ChoiceLens`) but the *named*
"moduli of readings" bundle — a single Lean `Moduli (C)` with the five instances
as its points, or `padic.md`'s named `Completion (base)` functor — is **ABSENT**.
This is the same shape as every "engine built, named object missing" entry in
`SYNTHESIS.md` §4(b).  Marking it honestly: the classification is real and
Lean-anchored piecewise; the *unifying named object* is a located target, not a
delivered theorem.

---

## 5. BUILT vs ABSENT (honesty pass)

**BUILT / ∅-axiom (grep + scan verified this session):**
- choice σ as a free section, σ-dependent operation: `ChoiceLens.lean:51,55,71,81`.
- the forced `C` axes (the OTHER side of the line): `ArityForcing.lean:41,66`,
  `ArityForcingGeneral.lean:79,91` — 0 DIRTY.
- presentation as a free parameter / real presentation-invariant:
  `PresentationDependence.lean:56 rcut_rescale`, `:110
  crossDetSmall_is_presentation_dependent`.
- base / completion-family pieces: `CauchyComplete.lean:38`,
  `Padic/Foundation.lean:41`, `Padic/Norm.lean:335`, `PrimeValuation.lean:96`.
- resolution as a composable graded shift: `ResolutionShift.lean:130
  IsResolutionShift_compose`, `Continuity.lean:64 compose_modulus_eq`.
- the moduli *carrier* (meet of a Lens-family): `IndexedJoin.lean:97 iProdLens`,
  `:82 iJoinLens_is_least`; carrier-polymorphic reading
  `PairCompletionUniversal.invert_is_the_universal_group_completion`.

**ABSENT (predicted / classified, not built):**
- a **named `Moduli(C)` 213 object** with the five free parameters as its points
  (the unifying bundle; §4c).
- a **single theorem "free L-param = section of a reading-fibration"** abstracting
  `ChoiceLens` + `ResolutionShift` + `PresentationDependence` to one `Section`
  predicate (the abstraction the way `PairCompletionUniversal` abstracts ℤ/ℚ₊/K₀).
- the **closed-vs-open-fiber sub-classification** (§2.2) as a Lean invariant
  (limit-fiber inhabited? = does the section converge or run).
- the forcing/independence prediction as a theorem (free section ⟹ both
  adjunctions consistent), as already flagged ABSENT in `axiom_of_choice.md`.

---

## 6. Summary for the seminar

- **Definition.**  A free L-parameter is a **section of a reading-fibration over
  one `C`** with inhabited fibers and **no canonical section** (no exterior
  dialer, §5.1).  Applying it is an act, ∅-axiom per-σ; the residue is σ-indexed.
- **Classification.**  choice σ / base / resolution / presentation / unforced
  tag-B are **one structure** — sections differing only in fiber-type — splitting
  into **closed-fiber sections** (genuine choice; predict AC-independence) and
  **open-tower sections** (cofinal narrowing; reached-by-none limit).  The
  binary-fiber section *is* the ±1 tag B (collapsing finding (vii′) into the
  family); the modulus is the open-tower section (re-deriving finding (v) without
  promoting it to a third invariant).
- **Moduli-of-readings.**  Its *carrier* is a built 213 object (`iProdLens`,
  `PairCompletionUniversal`); it carries the normal form one level up, its
  residue = the un-canonicalizability of the section (LLPO / reached-by-none).
  The *named* `Moduli(C)` bundle is ABSENT — a located target.
- **Forced/free line (the real structure).**  `C = (NS,NT,d,c)` is **forced** by
  the `ArityForcing` *theorem* (unique surviving section); `L`-params are **free**
  (many inhabited sections).  Both follow from the *one* axiom "no exterior
  dialer" (§5.1) — forced where the fibration has a unique section, free where it
  has many.  A wall would be an axis neither forced nor a section; the thesis is
  that none exists.

### Sharpest open question for Round 2

> **Is "the fibration has a unique surviving section" (forced `C`) versus "many
> inhabited sections" (free `L`) itself a decidable / `q=±1` property of a
> reading-fibration — and is the closed-fiber / open-tower split the SAME `q=±1`
> tag one level up (descent-terminates vs runs, `SYNTHESIS.md` finding (iii))?**

If yes, the forced/free dichotomy *is* the residue tag B applied to the
moduli-of-readings (forced = `q=+1` the section-search terminates at a unique
fixed point; free = `q=−1` it does not), and the entire L-parameter classification
collapses into the q=±1 spine — making "no walls" literally the statement that the
moduli-fibration's own tag is always defined (every axis is either a `+1`-forced
unique section or a `−1`-free open family, never undefined).  The buildable test:
a Lean `Section`/`Moduli(C)` object whose `q` is `ArityForcing`-uniqueness on the
`C` side and section-multiplicity on the `L` side, with `iProdLens` as the meet
and `ChoiceLens` as the multi-section witness.  That single object would close §4c
and §5's two top ABSENT items at once.
