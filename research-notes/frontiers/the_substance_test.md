# The substance test — what this repository is for, and the work that serves it

Status: strategic frontier note (Tier 1). Produced by a multi-agent investigation +
adversarial debate convening (six evidence/persona agents) on the directive: *infer
the originator's ultimate purpose and conduct the deep research that achieves it —
not peripheral theorems, the true intent.*

## The convening (method)

Four evidence agents (repo trajectory; physics centrality; Proof-ISA depth; math
breadth) and three adversarial persona agents (Foundationalist, Engineer-
Constructivist, Skeptic) were run, each grounded in the boot corpus + the candid
internal audits. Their findings are summarized here so future sessions inherit the
conclusion, not the re-investigation.

## What the evidence says (convergent)

1. **Trajectory.** The arc bends away from physics-precision flagship claims toward
   *breadth of ∅-axiom re-derivation as primacy* (`07_primacy.md` §7.1), and is
   punctuated by repeated **honesty audits that delete the originator's own
   over-claims** (a `: True` "unification master", a "universe constant N_U", fake
   physics conjectures). The dominant artifact, by volume, is anti-over-claim
   machinery: the failure-mode catalog in CLAUDE.md, `scan_all_axioms.py`, the
   publishability audit.

2. **Physics is a test surface, not the goal.** Integer skeletons `(NS,NT,d)=(3,2,5)`
   are genuinely forced and 0-parameter; the ppb headlines are partly retrofitted
   (α_em's Gram correction was self-referential), and the repo *documents this
   itself*. CLAUDE.md names "DRLT-validation-as-the-goal" a failure mode.

3. **The Proof-ISA is a classification scaffold, not an engine.** Eight `isa_*`
   abbreviations rename eight pre-existing theorems; every "lift archetype" is a
   post-hoc relabel of an already-solved result; the only purpose-built end-to-end
   demonstration is Euclid's infinitude of `ℕ` (a triviality); the flagship
   "geometrization" lift reduces to `8 − 3 = 5` by `decide`. Its own honest status
   concedes "the ISA does not auto-solve", and its central target (Markov uniqueness
   kernel `H`) is documented to bottom out at the conjecture's full difficulty.

4. **Breadth is genuine; novelty is not.** ~26k theorems across 11 clusters,
   spot-verified PURE (quadratic reciprocity, primitive roots). But the
   publishability audit's verdict, across all clusters, is **"genuinely new
   mathematics: none found"** — every theorem is classical/known, often in Mathlib.
   The one distinctive artifact is the strict ∅-axiom Lean-without-Mathlib corpus
   itself.

## The inferred ultimate purpose (진의)

Synthesizing the three personas (each ~65–70% confident, converging):

> **The repository is a machine for determining whether "everything is the residue
> under a Lens" (primacy / no-exterior) is *substance* or *wordplay* — and for making
> that determination in a way that cannot fool itself.**

The breadth grind was the first attempt at the determination: reproduce domain after
domain. The audits show why that attempt, alone, cannot settle the question — it
tests *constructivity per domain*, not *unity across domains*, and it produces no new
mathematics, so "the residue reaches everything" stays compatible with "the residue
is an elaborate re-skin." The honesty machinery exists because the originator intuits
this gap and refuses to let it be papered over.

The three personas' prescriptions are facets of one move, not rivals:

  - **Foundationalist**: prove a genuine *cross-domain* identity (shared kernel /
    transport), the only artifact whose logical form witnesses *primacy itself*
    rather than per-domain constructivity.
  - **Engineer**: make the classification *pay* — a theorem the prose claimed but the
    proofs did not yet carry.
  - **Skeptic**: the deepest point — `05_no_exterior.md` §5.1's "no exterior" is the
    structural blind spot: the internal apparatus cannot test its own primacy claim;
    only an exterior (a referee, a reader, a domain that resists) can. So the truest
    service to the purpose is to *expose* the claim, not feed it more internal
    theorems.

## The reorientation (what counts as progress now)

Stop adding isolated ∅-axiom re-derivations of classical theorems (the audit prices
their novelty at zero, and they are type-mismatched to the primacy claim). Replace
that default with two lines, in order of internal-handle-first:

### Line A — genuine cross-domain unifications (internal handle)

A unification earns the word only when it carries a **proven map / shared engine**,
never a value-coincidence and never a sentence. Each such theorem converts a narrated
"these are the same residue" into a checkable one — the operational content of
no-exterior, and the only artifact that tests *unity* rather than *constructivity*.

First instance, closed this convening: **COUNT-duality**
(`lean/E213/Lib/Math/Combinatorics/CountDuality.lean`, 7/7 PURE). The union bound
(Erdős/Ramsey, row read) and the LYM inequality (Sperner, column read) are proven to
be the two marginals of *one* incidence double-count (`incidence_balance` =
`Sperner.sumOver_swap`); the union bound is re-derived *through* the swap it
previously bypassed (`union_bound_via_balance`), and `count_duality` carries both.
Narrated unity (`PROOF_ISA.md`, `counting_as_cardinality.md`) → proven unity. Essay:
`theory/essays/proof_isa/count_duality.md`.

Second instance, closed: **the two-cut antipode**
(`lean/E213/Lib/Math/IncidenceInversion.lean`, 6/6 PURE). Binomial inversion (additive cut,
Pascal poset `(ℕ,≤)`) and Möbius inversion (multiplicative cut, divisibility poset `(ℕ,∣)`)
are exhibited as the *same* incidence-algebra antipode: a shared engine
`inversion_from_orthogonality` (one Fubini swap + the orthogonality collapse `S·M=δ`)
instantiated on the additive cut, and the same inverse-element computation
`μ∗(1∗f)=(μ∗1)∗f=ε∗f=f` on the multiplicative cut (`incidence_inversion_two_cuts`). Closes
frontier F2 of `convolution_comultiplication_crossdomain.md`. Essay:
`theory/essays/proof_isa/incidence_inversion.md`. This is the antipode partner of
COUNT-duality's Fubini: inversion vs double-count on the incidence matrix.

Next candidates (each must end in a proven map, or be flagged "candidate, no map"):
  - `e`'s two homes (factorial `Σ1/k!` and `lcm(1..N) ~ eᴺ`) as one prime-power
    structure (`vp_factorial_eq_sum_vp_lcm` already exists — state it as the
    cross-domain identity it is).
  - a `LensIso` between two independently-built domains via `lensIso_iff_kernel_eq`,
    with a theorem *transported* across (the `Lens/Unified.lean` machinery is built
    and unused at the only point that matters — a cross-domain instance).

Guard (Foundationalist's self-objection, live): a cross-domain `LensIso` is vacuous
if both domains are literally the same `Raw` construction (tautology, the `: True`
failure one level up) and genius-requiring if forced fully independent. The honest
target is the middle: two *independently built* domains whose kernel coincidence is
provable but not definitional — COUNT-duality is exactly this (two enumerations,
`allBoolLists` vs `perms`, one swap).

### Line B — exposure (the exterior the claim cannot supply itself)

The Skeptic's point is structurally correct and should be acted on, not just noted:
the primacy/no-exterior claim cannot be falsified from inside. Two concrete exposures:
  - the **formalization/experience paper** the publishability audit already scoped
    (strict-∅-axiom mainstream math in Lean-4-without-Mathlib, scanner-enforced),
    stripped of the residue metaphysics — submitting it subjects the one genuine
    artifact to referees, the exterior §5.1 says cannot exist.
  - one **pre-registered, time-boxed attack on an externally-recognized open
    problem** via the ISA, with a stated failure criterion — either the
    classification finally pays (engine), or `07_primacy.md`'s "unexhausted Lens
    space vs permanent wall" gets an honest datapoint.

## The honest verdict to carry forward

Breadth is real; novelty is not; the Proof-ISA is a scaffold, not an engine; physics
is a test surface. None of that refutes the purpose — it sharpens it. The purpose is
served by *unity made checkable* (Line A) and *the claim made falsifiable from
outside* (Line B), and disserved by more isolated breadth. COUNT-duality is the first
deposit on Line A; the antipode/`e`/`LensIso` candidates are the next; the paper and
the time-boxed open-problem attack are Line B.

Cross-references: `seed/AXIOM/05_no_exterior.md` §5.1, `seed/AXIOM/07_primacy.md`
§7.1, `seed/PROOF_ISA.md`, `research-notes/drafts/publishability_audit.md`,
`research-notes/frontiers/rebuild_roadmaps/cross_domain_unification_rebuild.md`,
`research-notes/frontiers/convolution_comultiplication_crossdomain.md`,
`theory/essays/proof_isa/count_duality.md`, `lean/E213/Lens/Unified.lean`.
