# General-theory meta-analysis — a long-term program

**Goal**: discover *genuine general theoretical structures* in the 213/DRLT
corpus by deep analysis + meta-analysis of recurring statement patterns across
Lean modules and theory documents — and separate them from coincidental
resonances / forcible maps using the adversarial debate method
(proponent / skeptic / formalist) that the slot-tower arc validated.

**Discipline (carried from the slot-tower marathon, `slot_tower_debate.md`)**:
a candidate "general structure" earns the label only if it is one of —
1. **shared mechanism**: one schema doing *generic work*, ≥2 genuine instances
   (e.g. `OrderWrap.no_order_of_wrap` — wrap kills every order witness);
2. **pinned distinction**: a binary/orthogonal *difference* with a real
   theorem on each side (e.g. bridge 1 finite/infinite certificate; bridge 4
   vector/sign).
— and is rejected if it is —
3. **vacuous container** (`{cert, iff}` / `LeveledReadout`: a tautology with no
   generic consumer), or
4. **resonance only** (a numeric/phenomenological coincidence with different
   objects/mechanisms — §5(b) level-2 ceiling vs `^`-wall).

Every Lean claim must be ∅-axiom (`tools/scan_axioms.py`).  Findings recorded
here; closed ones promoted to `theory/`.

## Candidate general structures under investigation

(Each gets: survey → debate → formalize-or-reject → record.)

- **C1. Equality = faithful readout agreement; discreteness = finite support.**
  Seed evidence (bridge 1, this branch): `cutEq` *defines* equality as per-level
  readout agreement; `vp_separation` is the *theorem* that the prime readout is
  faithful; `vp_eq_zero_of_gt` (finite support) vs `cut_no_finite_certificate`
  (unbounded) pin the discrete/continuum axis.  General question: do *all* 213
  equality notions factor through one readout-faithfulness shape, and is
  "discrete ⟺ faithful readout has finite support" a general theorem?

- **C2. Commutativity = order-forgetting = atom-indistinguishability =
  simultaneity.**  The repo asserts this as "one handle" (CLAUDE.md;
  `slot_tower_crossdomain.md` §5).  General question: is there a single Lean
  structure of which `add_comm_from_append`, `mul_comm_from_grid`,
  `conv_comm`, `append_comm` are instances — commutativity ⟺ a transpose/swap
  symmetry of the generating operation?

- **C3. The "regularity ceiling" typology.**  Where regularity runs out
  (`^`-wall, ORIGIN_RAW level-2, `mod p` wrap, no-finite-certificate).  §5(b)
  ruled level-2 vs `^`-wall a *resonance*.  General question: is there a
  genuine meta-structure to "ceilings", or are they all distinct?  (Default:
  skeptical — likely resonance, per the §5(b) precedent.)

- **C4. The meta-theory of genuine-vs-forcible itself** (the decision
  procedure above).  Synthesised from this session's validated/rejected cases.

## Log

- (init) Program opened; surveyor team dispatched on C1–C3; C4 synthesised
  from the slot-tower marathon record.

## Survey results

### C2 — commutativity / atom-indistinguishability → DIFFERENT MECHANISMS, one PRINCIPLE

Surveyed every `*_comm` proof and its *mechanism* (not statement):

| op | theorem | proof mechanism | what the readout erases |
|---|---|---|---|
| append | `UnitList.append_comm` | bare list induction (base fact) | — (the floor) |
| `+` | `UnitList.add_comm_from_append` | `count (l₁++l₂) = count (l₂++l₁)` via `append_comm` | **order** |
| `×` | `UnitGrid.mul_comm_from_grid` | grid transpose preserves cell total (`heads_tails_total`) | **layout** |
| `conv` | `Convolution213.conv_comm` | split-endpoint reversal of `natSplits` | **cut-endpoint order** |
| `^` | `HyperAssoc.pow_not_comm` | `decide` witness `2^3≠3^2` | **nothing** (base/exp distinguishable) |

**Verdict**: the asserted "one handle" (comm ⟺ atom-indistinguishability ⟺
simultaneity) is **not** a shared Lean schema — the three comm proofs cite
genuinely different crux lemmas (`append_comm` / `heads_tails_total` /
`conv_peelL/R`); indistinguishability is *embedded in each structure*, never
*invoked as a hypothesis*.  A `comm_iff_atoms_indistinguishable` schema does
not factor.  **But** a genuine general *principle* is real: **commutativity =
invariance of the defining readout under the generating structure's reordering**
— "what the structure forgets is what commutes."  `+`/`×`/`conv` each commute
because their readout (`count`/`total`/the cut) is invariant under a
structure-specific swap; `^` commutes nothing because its readout forgets
nothing.  This is **type-(2)** (a shared principle whose instances do not share
a proof), not type-(1) shared mechanism.  [Refined candidate C2′ below.]

### C3 — regularity ceilings → RESONANCE ONLY (no general ceiling theory)

Enumerated 9 boundary phenomena (`^`-wall comm/assoc; `^`-wall fold/transcendence;
ORIGIN_RAW level-2 past-completeness; `mod p` wrap; cut no-finite-certificate;
vp finite support; PairOp bi-distributivity impossibility; Raw determinism
step1→3; async MemEq depth).  Applied the §5(b) four-axis test (same objects?
same symmetry/predicate? same mechanism? or numeric coincidence?) to every
candidate pair.

**Verdict**: every cross-phenomenon unification is **rejected** except the two
already-closed genuine ones (`OrderWrap.no_order_of_wrap` schema; `HyperLadder`
recursion) and the one pinned distinction (finite/infinite certificate).  The
"regularity runs out at a rung" shape is *phenomenological*, not a mechanism;
the breakdowns have independent causal stories (type-promotion vs syntactic
subterm-closure vs orbit-wrap vs support-finiteness).  A general "ceiling
theory" would require provably-false bridging lemmas — stereotype-matching.
No deliverable, by design.

## Emerging meta-theorem (C4) — the architecture of 213 unification

The two surveys converge on a **substantive structural claim about 213 itself**,
corroborated by the whole slot-tower marathon (bridges 1–4, §5 a/b):

> **Genuine type-(1) unification (one schema, one shared proof, ≥2 instances)
> is RARE in 213 — essentially `OrderWrap` and `HyperLadder`.  The corpus's
> apparent cross-domain unity is overwhelmingly type-(2) *pinned distinction*
> or type-(3) *resonance*.  The residue does not collapse domains into common
> mechanisms; it reproduces them with their distinctions intact.**

This is not a defeat — it is the `no-exterior` / `object1_not_surjective`
theme made precise at the meta level: *no single view unifies the domains*
(the residue is outside every view's image), so most "unifications" a naive
search proposes are forcible maps the structure rejects.  The **decision
procedure** that sorts them is itself the reusable general tool:

1. propose a single schema;
2. **generic-consumer test** — does a theorem do *generic work* over the
   schema (rule something out / derive something), or is it a tautological
   `{data, iff}` container? (kills type-4: LeveledReadout, naive comm-schema);
3. **four-axis test** — same objects / symmetry / predicate / mechanism, or
   numeric coincidence? (sorts type-1 vs type-3);
4. if neither a shared proof nor a coincidence, look for a **theorem on each
   side pinning a genuine binary/orthogonal difference** (type-2).

C4 is a `theory/` meta-chapter, not a Lean theorem (it is *about* the corpus).
C1 (equality/readout) pending — the strongest *formalizable* candidate.

### C2′ — comm = readout-erasure: non-vacuity check → SCHEMA VACUOUS, PRINCIPLE GENUINE

Applying step 2 (generic-consumer test): the schema
`op a b = R (gen a b)` + `R (gen a b) = R (gen b a)` ⟹ `op a b = op b a`
is a **tautology** — `op`-commutativity literally *is* the readout-swap-
invariance, so the "schema" restates its own hypothesis (the same defect
that killed `LeveledReadout`).  The genuine content is entirely in proving
the swap-invariance per structure (`append_comm` / transpose / split-reverse).
So C2′ is **not** a type-(1) schema.  Verdict: principle genuine, schema
rejected — consistent with the decision procedure.

### C5 (emergent, the strongest cross-cutting candidate) — faithfulness ⟂ commutativity

C1 and C2 *cross*.  Read an operation as `op a b = R (gen a b)` (a readout `R`
of a generating structure `gen`).  Then:

- **forgetful `R` (large fibers) ⇒ commutativity.**  `+` = `count` of a list
  (forgets order, `add_comm_from_append`); `×` = `total` of a grid (forgets
  layout, `mul_comm_from_grid`).  What `R` erases is precisely the swap.
- **faithful `R` (trivial fibers) ⇒ NON-commutativity.**  At `^` the readout
  keeps base/exponent in *different slots* (the `iter` count vs the iterated
  `f`), so the swap is visible — `pow_not_comm`.  The prime readout `vp` is
  *faithful* (`vp_separation`, UFD) — and it is exactly the `×`→`^` rung where
  the exponent vector "remembers which prime" (`vp_mul`) that commutativity
  dies.

So **commutativity and readout-faithfulness are dual**: the *same* property
(how much the readout forgets) that makes the equality-certificate small/large
(C1: finite support = discrete = faithful-and-finite) governs whether the
operation commutes.  The tower is the ladder of *decreasing forgetting*:
`append` (keeps order) → `+`/`×` (forget order/layout, commute) → `^` (keeps
the slot split, faithful, non-comm).  This ties C1 (faithfulness / certificate
size), C2 (commutativity), and the `HyperLadder` tower into one axis:
**how much the readout forgets**.

Pending C1 confirmation of the faithfulness inventory; then test whether the
duality has a *non-vacuous* Lean core (the "faithful `R` + non-symmetric `gen`
⇒ non-comm" direction may do genuine work, unlike the tautological forward
direction) or is itself a type-(2) principle.
