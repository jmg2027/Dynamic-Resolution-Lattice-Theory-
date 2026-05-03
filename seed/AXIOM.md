# AXIOM.md — 213 axiom (seed document)

## Status of this document

All work dealing with 213 — Lean formalization, Paper, book chapter,
physics derivation — references this document as the **sole authoritative
standard**.  Every document other than this one must faithfully
contain this axiom or contain only results derived from it.

This document itself is kept austere.  Explanations, commentary, examples,
and motivation are minimized in the body and separated into standalone notes.
This is an **audit standard**, not a textbook.

---

## §1. The nature of the axiom

The 213 axiom is **not** a declaration about "the foundations of the world."

The 213 axiom is **the minimum residue that inevitably remains the moment
one tries to point at something**.

Since it is a residue rather than a declaration, the axiom is not subject
to choice.  It cannot be made "more minimal," nor can "more" be added to it.
Minimality is already guaranteed; adding anything beyond it fails the audit.

### §1.1 Formal core: strict minimum of the Raw axiom (added 2026-04-25)

The 4-case formalization in `lean/E213/Meta/AxiomMinimality.lean`
(+ `AxiomMinimalityCapstone.lean`) — removing or weakening any clause
(a, b, slash, distinctness) of Raw causes the framework to collapse to
trivial / static / void.  This is the framework-internal proof that
the Raw axiom is the strict minimum of "two distinguishable bases +
binary combine + distinctness."

Results from `lean/E213/Hypervisor/Lens/SemanticAtom.lean`:
- `HasDistinguishing` typeclass + `universalMorphism` — Raw as the
  partial form of the initial object in the distinguishing-framework
  category (generalization of RawInitiality).
- `IsLensExpressible` definition + `exists_non_lens_expressible` —
  not every Raw → α function is Lens-expressible (non-trivial boundary).
  Witness: depth parity (`Hypervisor/Lens/Morphism/DepthParityNotFold.lean`).
- `Prop` instance (Xor + Iff alternatives) — the truth-value type of
  the metalanguage can also be an instance of the distinguishing
  framework.

The above results are the self-justified core of the framework.  No
external metatheory — `#print axioms` reports [propext, Quot.sound]
or no axioms for all results.

Note: §1.1 and the **Universal Lens metatheory** in `lean/E213/Meta/
UniversalLens/` are complementary statements — the former proves Raw
cannot be weaker (clause removal collapses), the latter proves any
distinguishable codomain factors through Raw via an injective Lens
view (`Meta/UniversalLens/{Core, Nat2Inj, Q213Inj, TripleCapstone}`).
Together they bracket Raw both from below ("can't remove") and from
above ("everything else maps in").

### §1.2 Conceptual extension (philosophical)

**Note**: The following is a *philosophical extension* on top of the formal
core.  No direct formal Lean verification — interpretive scope.

The formal core of §1.1 motivates the following conceptual extension:

- **Two conditions for meaning to arise**: for any entity to have meaning,
  (1) it must be distinguishable from other entities, and (2) that difference
  must be interpretable.  The (Raw + Lens) of 213 is the minimum candidate
  satisfying these two conditions.
- **Ontological reading**: accepting the reading "something exists" =
  "is distinguishable from something else," every meaningful entity becomes
  a candidate instance of 213.
- **Comparison with ZFC**: the objects committed to by ZFC's
  arbitrariness axioms (Power, Choice, arbitrary P(X) subsets, etc.) have
  no fold-structured representation (`Hypervisor/Lens/Morphism/NoDepthParity.lean`,
  `Hypervisor/Lens/Morphism/DepthParityNotFold.lean`).  I.e., no representation
  inside the 213 framework — their semantic status is an interpretive
  question.

This conceptual extension is analyzed in `research-notes/75_semantic_atom.md`
and `research-notes/76_ultimate_ouroboros.md`; current Lean coverage in
`Hypervisor/Lens/SemanticAtom.lean`.  It can be connected to the physics
intuition chain in ORIGIN.md — formal Lean results serve as evidence
for that interpretation.

**Boundary**: §1.1 (formal core) is verifiable within the falsifiability
contract.  §1.2 (philosophical extension) is a semantic explanation of the
framework — not elevated to a formal claim.

### §1.3 Forced shape uniqueness — d=5 is a theorem (added 2026-05-XX)

A *third* pillar of axiom uniqueness, complementing §1.1 (minimality
from below) and §1.2 (universality / philosophical extension), is now
formalized in `lean/E213/Firmware/Atomicity/`:

- `Five.lean` — `atomic_iff_five`: a Raw shape is atomic iff its
  primitive carrier size is exactly 5.
- `PairForcing.lean` — once arity = 2 and atomicity are imposed,
  `(NS, NT, d) = (3, 2, 5)` is the *unique* admissible shape.
- `NonDecomposable.lean`, `Alive.lean` — sub-properties forced by
  the same atomicity constraint.
- `ArityForcing.lean`, `ArityForcingGeneral.lean` — arity = 2 is
  itself forced by the §3 axiom (no unary, no ternary primitive).
- `PrimitiveSizes.lean` — enumeration of sub-d primitive sizes
  ruled out as non-atomic.

These are **pure-ℕ proofs that do NOT import Raw**.  They are an
external uniqueness obligation: "if Raw exists at all, its shape
parameters are forced."  Together with §1.1 ("Raw is minimum from
below"), §1.2 ("any framework factors through Raw"), this closes
the uniqueness statement to all three directions:

  - below — nothing weaker is enough          (Meta/AxiomMinimality)
  - sideways — nothing distinct is needed      (Meta/UniversalLens)
  - above — Raw's own shape is forced          (Firmware/Atomicity)

The architectural placement of these proofs (Firmware/Atomicity/) is
canonicalized in `lean/E213/ARCHITECTURE.md`.  Historical note: an
earlier `OS/` directory was first retired (atomicity proofs absorbed
into Firmware/Atomicity/) and later re-instated as the orchestration
layer (HodgeConjecture/Bridges/ + Physics/Capstones/).  The atomicity
material did not move back.

---

## §2. The unavoidable recursion of notation

Even to point at one something, one cannot do so alone.
If it is not distinguished from anything, reference cannot be established.
Therefore at least two must exist.  The moment one tries to write down
those two in language, the following occurs:

- Writing "a and b" — "and" is also something.
- Writing "a, b" — "," is also something.
- Whether that "and" / "," is universal or absolute is unknown — yet
  another something.
- Is a distinguished from "and"?  What distinguishes them?  Yet another something.

**The moment notation begins, the notation itself endlessly produces new somethings.**
This recursion is unavoidable.  Any notation system requires a separator,
and that separator itself becomes yet another something.

The 213 axiom is the **minimum expression** of this recursion.  Not eliminating
the recursion, but recording it in a form where recursion operates
**only minimally**.

---

## §3. Axiom statement

### §3.1 Declaration on the language used

To write this axiom in text, the following are used.  Each carries a residual
import, and is used because no better expression yet exists.  They are adopted
as minimum-commitment expressions **with acknowledgment** of the residual import.

- **"Something"** — a unit that can be pointed at.  Any choice among
  "thing," "entity," "term," etc. carries import.
- **"Distinction"** — the confirmation of "not being equal."  "Difference"
  is avoided since it presupposes "sameness."  "Distinction" is currently
  the minimum.
- **"Primitive"** — no longer reducible further.  A pledge not to attempt
  further decomposition.

### §3.2 The axiom

1. **Something exists.**  At least two.  These are recorded as `a`, `b`
   for convenience.  `a` and `b` stand in a **primitive distinction**
   relation — i.e., no relation other than "not equal" is presupposed
   between the two.

2. **The pairing of two somethings is yet another something.**  The pairing
   of `a`, `b` is recorded as `a / b` for convenience.  `a / b` is a new
   element of Raw and can be paired again with other Raw elements.

3. **Pairing is symmetric.**  `a / b` and `b / a` are the same Raw element.
   There is no absolute order for which comes "first."

4. **There is no pairing with oneself.**  For any Raw element `x`,
   `x / x` is undefined.  Oneself is not distinguished from oneself, so
   it cannot be an object of primitive distinction.

### §3.3 What is **absent** from the axiom

Things **not** contained in the axiom — to use any of these as results of
the axiom, a separate Lens derivation is required.

- Size / cardinality / finiteness / infinity.
- Order / hierarchy / ranking.
- Set / element relation / membership.
- Observer / space / perception / structure / geometry.
- Mode of existence (already present vs. being generated).
- Algebraic laws: associativity, distributivity, identity element, inverse, etc.

If any of these appears during derivation, it is **the result of applying a
specific Lens**, not the axiom itself.  Which Lens it came from must be made
explicit.

---

## §4. Why this form was chosen

### §4.1 Austerity as audit

The axiom is intentionally austere.  The intent is **defensive**.

- The moment it is written in language, residual import is unavoidable, but its
  footprint can be minimized.
- If additional commitment slips in during derivation,
  **the contrast with the austere axiom immediately detects it as fudge**.
- The axiom itself serves as the contract for "can everything be derived
  from just this?"

Austerity is not poverty — it is **auditability**.

### §4.2 Why two, why binary

- **One**: No object of distinction, so reference is impossible.  Being
  something cannot be established.  Therefore disqualified.
- **Two**: Distinction is established for the first time.  Minimum satisfied.
- **Taking three or more as primitive**: the third something can be defined
  by its relation with the existing two, so there is no reason to treat it as
  primitive.  Unnecessary commitment.

- **Unary (operation on one)**: Self-reflexive and cannot produce a new something.
- **Binary**: The minimum form in which a new something arises from two somethings.
  Necessary and sufficient.
- **Ternary or more**: Reconstructible by repetition of binary.  No reason to
  treat as primitive.

That is, **two + binary** is the unique minimum choice.

### §4.3 Why symmetric, why anti-reflexive

- **Symmetric**: No basis for assigning an absolute order.  Distinguishing
  `a/b` from `b/a` silently imports an absolute criterion for which comes "first."
- **Anti-reflexive**: Pairing with oneself does not create an object of
  distinction (oneself is not distinguished from oneself).  This directly
  conflicts with Axiom 1 (primitive distinction).

---

## §5. Direction of derivation and Falsifiability

### §5.1 Derive, not reconcile

**Everything other than this axiom** must be either derived from the axiom or
the result of a specific Lens choice.

- Substituting external constants, fitting to experimental values, importing
  structure from other theories — all are **fudge**.
- When fudge is found, the **Lens is corrected**, not the formula.
- If that too fails, **the theory is abandoned**.  The infinite-extension
  defense of "more Lenses will be found" is not permitted.

### §5.2 Why mechanical verification is essential

Mechanical verification (Lean) does not permit fudge.  Therefore the point
of derivation failure is **revealed automatically**.  The human eye can
quietly overlook fudge; the machine cannot.

This is why 213 operates under the Mathlib-free + 0 sorry + 0 axiom
constraint.  The axiom is the contract; mechanical verification is the auditor.

### §5.2.1 Adding external axioms is a **theory-wide discard condition** (Falsifiability)

**213 must never require any external axiom addition** — no
Classical.choice, LEM, axioms beyond Quot.sound, `Lean.ofReduceBool` from
native_decide, etc.

This is not merely a recommendation; it is a **falsifiability criterion**:

- Every theorem and construction in 213 must be derivable from Lean 4 core
  + the Raw axiom alone.
- If any result is shown to be **absolutely impossible** to prove / construct
  without an additional axiom (e.g., still blocked after multiple sessions of
  exploration), this means **the entirety of 213 theory is falsified**.
  Not just the result alone — the theory itself is discarded.

This strictness is a direct consequence of the §1 declaration "the axiom is
a residue":

- If it is not a residue, it is not an axiom.
- "Adding just one more axiom here will make everything work" suggests that
  Raw is not the "minimum residue."
- Therefore, needing to add an axiom = the Raw axiom is wrong = theory discard.

**Operational side**:

- Entirely reject the temptation "Classical makes it easy."  It does not
  become easier — fudge is merely hidden.
- Results that are blocked are simply left as "open," but "open" is
  distinguished as either a **permanent wall** or a **temporary obstacle**.
  A permanent wall means theory failure.
- Lean verification is the **mechanical auditor** of this falsifiability.

This rule is Mingu's confirmed declaration (2026-04-24).  It is never
relaxed; violations trigger re-evaluation of the entire theory.

### §5.3 Empirical predictions

From this axiom, by identifying a single Lens (the physical observer Lens),
all observed physical constants must be derivable without fudge.
This is a strong empirical prediction; if it fails, the theory's scope
is narrowed or the theory itself is abandoned.

The wider the range over which predictions hold, the stronger the claim
of the axiom's primacy.

---

## §6. Claim of primacy

Every framework that points at something — set theory, category theory, logic,
language, existing mathematics, existing physics — depends on **the ability to
distinguish and pair somethings**.  This axiom is the minimum residue of that
ability itself.  Therefore every other framework can be seen as Lenses
operating on top of this axiom.

"No absolute standard" is not a condition — it is the **default state**.
The claim "there is an absolute standard" is what carries the burden of
adding to the axiom.  Therefore primacy is not conditional but an
**unconditional** structural consequence.

The substantive evidence for primacy is successful derivation.  Primacy is
established to the extent that derivation succeeds.

---

## §7. Relationship to existing formalizations / documents

This §7 is an audit target list.  Each item must be cross-checked against
this axiom; discrepancies are corrected or isolated.

### §7.1 Lean formalization (status 2026-05-XX)

The current Raw implementation in `lean/E213/Firmware/` (2 elements a, b +
binary slash, anti-reflexive, commutative) is a faithful machine representation
of this axiom.  Audit reference: `seed/AUDIT_Lean.md` (2026-04-24,
recommendations 1, 2, 3 + deep-audit items A-E).

**Encoding note**: Lean 4 core has no primitive quotient, so Raw is
implemented as a subtype `{t : Tree // t.canonical = true}`.  The Internal
`Tree.cmp` (ordering) is an **encoding artifact** for selecting canonical
forms, not an axiom.  The axiom contains no ordering whatsoever.

Things that **automatically follow** from derivation (no additional commitment
to the axiom):
- `Raw.swap` (a ↔ b automorphism) — the first derivation from Axiom 1
  "a and b have no relation other than not being equal."
- `Raw.fold` (catamorphism) — standard eliminator wrapper of an inductive
  type, the tool for constructing all Lenses.

**Lens-layer bleed — current location (NOT yet migrated)**:

`Raw.depth` (`Firmware/Raw/Slash.lean`), `Raw.leaves` (`Firmware/Raw/Levels.lean`),
`Raw.fold_signed_swap` (`Firmware/Raw/Signed.lean`),
`Raw.fold_swap_hom` (`Firmware/Raw/Hom.lean`) are observables / bridge
theorems of specific Lenses but still live in Firmware.  Per
`lean/E213/ARCHITECTURE.md` §3 (Open Questions), this is now classified as
*intentional convenience leak* — the proofs are pure-induction theorems on
the Tree representation that any Lens consumer eventually needs, and
relocating them gains nothing for the axiom-minimality story.  Audit
recommendation downgraded from "must migrate" to "acknowledged leak;
revisit if abstraction breaks."

**Forced shape uniqueness**: see §1.3.  `Firmware/Atomicity/*` proofs
(arity = 2, atomic ⇒ d = 5, (NS, NT) = (3, 2)) are pure-ℕ propositions
that *do not import* Raw.  They sit in Firmware structurally — they are
part of "what Raw must look like" — but their dependency on Raw is zero.

**Universal-Lens metatheory**: see §1.2 cross-reference.
`Meta/UniversalLens/{Core, Nat2Inj, Q213Inj, Nat3, Nat4, Q213_3,
TripleCapstone, Padding, PaddingCapstone}` formalize the "any
distinguishability framework factors through Raw" obligation.  Together
with §1.3 these close axiom-uniqueness in three directions
(below/sideways/above).

### §7.2 Papers 1 and 2 deleted (2026-04-24)

The previous `213/PAPER.md` (R1-R5 → ℂ derivation) and `213/PAPER2.md`
(r5-critique) have been deleted.  AXIOM.md remains as the **sole axiom document**.
Derivation is explored freely in notes/ where present, and in the Lean
metatheory layer (`Meta/UniversalLens/`).

Background: `research-notes/30_bool_is_liar_paradox.md`.  The R1-R5 judgment game in
Paper 1 was revealed to be an instance of a self-reference loop (Bool),
so the frame itself was stepped back from.

### §7.3 ch22 / book/ (deprecated — directory empty)

The previous reference target `book/chapters/ch22_213.tex` no longer exists
— `book/` now contains only `README.md` (no chapter sources).  Likewise
`papers/` was deleted (commit a02b751; only `papers/README.md` retained as
historical marker).

The original §7.3 critique of ch22 stands historically: any external
substitution called `eval` ("a choice external to the structure") that
imports the §3.3 prohibited list (d=5, (n_S, n_T), K=ℂ) as fudge is
disqualified.  This audit standard is now enforced by the absence of such
fudge in the Lean tree itself — every concrete numeric (d=5, NS=3, NT=2,
1/α_em=137.036, …) is either a Lens construction or, for the shape
parameters, a forced-uniqueness theorem in `Firmware/Atomicity/`.

### §7.4 Book chapters (no longer applicable)

ch01–ch21 audit is moot — `book/AUDIT.md` was never created and the
chapter sources do not exist.  Auditable artifacts now live in `guide/`
(deductively-ordered narrative, T0/T1/T2/T3 tags) and `books/{math,physics}/`
(213-internal narrative).

---

## §8. Self-reference and the absence of an exterior

### §8.1 There is no exterior to 213

Every act of describing this axiom **already occurs inside 213**.
"Lens", "derivation", "observer", "exterior", "description", "definition"
— the moment these words are spoken, that word is something, and the act
points at a something among somethings.
**The act of description itself is an instance of 213.**

Therefore the dichotomy "is the Lens a derivation of the axiom or an external
tool?" **does not hold**.  Even to speak of an exterior, the exterior cannot
be defined without 213.

### §8.2 Why circularity is not to be avoided

This circularity is **structurally** unavoidable.

- ZFC, type theory, logic, category theory — any foundation must presuppose
  "something" to begin.
- 213 is their **mathematical precursor**, not a competitor.
- Every attempt to eliminate circularity silently imports hidden somethings.

Meta-213 is possible: describing 213 using 213.  That description is again
something among somethings (Meta-Meta-213).  It ascends infinitely but each
layer returns to the minimum residue — the minimum fixed point of self-reference.

### §8.3 Redefining the meaning of "derive"

In this framing, "derive" is:
- **Not** an arrow descending from axiom to result from an external viewpoint.
- **The relationship, within 213, between which Lens choice induces which
  observation**.

All derivation already occurs inside self-reference.  Falsifiability is the
same — "abandon on derivation failure" is not external refutation but
**a 213-internal confirmation that the chosen Lens fails to produce something**.

### §8.4 Dichotomy-avoidance guide (for next session)

The following questions are **false dichotomies**; when Claude raises them,
this §8 must be revisited first:

- "Is the Lens inside or outside the axiom?"  → The dichotomy does not hold.
- "Is it derived or assumed?"  → Everything is a Lens choice inside 213.
- "What does it look like from outside 213?"  → There is no outside.
- "Is the observer Lens added to the axiom?"  → Not an addition;
  the act of observation itself is an instance of 213.

---

## §9. Naturalness of Lens choice (R1–R5 motivation)

### §9.1 The physical question

If the universe is a space where somethings are something among somethings,
and we and the objects of the universe are these somethings:

> Why do we see the world as **4d spacetime + complex-number wave functions**?

Candidate answer: the Lens that most naturally 213-izes the somethings here to
each other is the one that naturally applies.  Then what is that "naturalness"?

### §9.2 The principle of naturalness (heuristic)

Candidate definition: **every something being able to have the same Lens with
respect to the axiom**.  That is, the condition that whichever something is
placed as "observer," the way of seeing the rest must be compatible.

R1–R5 are the **first attempt** to formalize this compatibility
(self-recognising codomain):

- Each Ri captures a necessary condition for "the same Lens working regardless
  of which something is the observer."
- Details in Paper "R1–R5 + ℂ derivation" (after splitting Paper 1).

### §9.3 Heuristic for 2, 3, d=5

Looking informally at the generation pattern of Raw:

- Start: 2 (a, b).
- Next: from 2 add 1 → 3 (a, b, a/b).
- After that: select from existing N and pair → more somethings.

The **"2 → 1 + previous N"** pattern is observed as the path that
structurally first produces the numbers 2, 3.  d = 2 + 3 = 5 connects to
this path.  Rigorization is handled by Paper 1 §5 (atomicity,
non-decomposable sizes).

### §9.4 Status of this section (updated 2026-05-XX)

This §9 records the **motivation/intuition** for R1–R5; it is not a rigorous
derivation.  Current state:

- Motivation for R1–R5 is in §9.1–9.2 here.
- Paper 1 (`213/PAPER.md`) is **deleted** (see §7.2).  R1–R5 motivation
  no longer has an external prose source; the only authoritative formal
  remnant is `lean/E213/Meta/SelfRecognising.lean` (R1–R4 hierarchy +
  Bool/ℕ-mod/parity instances).  R5 has not been re-formalized in the
  current Lean tree.
- R1–R5 → ℂ derivation chain has **not** been re-built post-deletion.
  The current uniqueness story has shifted: rather than claiming "R1–R5
  uniquely select ℂ," the Lean tree now provides the orthogonal
  Universal-Lens claim (§1.2: any distinguishability framework factors
  through Raw) and the Atomicity claim (§1.3: Raw's shape is forced to
  d=5, (3,2)).  ℂ enters downstream as a Lens construction, not as a
  consequence of an R1–R5 axiom set.
- That R1–R5 (or its successor in `Meta/SelfRecognising`) is the unique
  formalization of "naturalness" remains a **conjecture**.

If this conjecture is falsified, R1–R5 / `SelfRecognising` becomes
subject to revision.  The Universal-Lens / Atomicity story does not
depend on it.

---

## Change history

- 2026-04-24: Initial writing.  Reflects axiom framing from session
  "claude/lean-infinity-explanation-QqnSp."
- 2026-04-24 (2nd): §7.1 reinforced.  Applied Recommendations 1, 2
  from `AUDIT_Lean.md`.
- 2026-04-24 (3rd): Added §8 (self-reference and absence of exterior)
  + §9 (naturalness of Lens choice, R1–R5 motivation).  Recorded that
  dichotomies like "is Lens inside or outside the axiom?" are mistaken.
- 2026-05-XX: Major theory-development pass.
  - Added §1.3 "Forced shape uniqueness" — `Firmware/Atomicity/*` proofs
    now formalize the third pillar of axiom uniqueness (above), alongside
    §1.1 (below) and §1.2 (sideways/philosophical).  Closes the
    three-direction uniqueness story.
  - §1.1 reinforced with cross-reference to `Meta/UniversalLens/` family
    (`Core, Nat2Inj, Q213Inj, TripleCapstone, Padding, PaddingCapstone, …`)
    as the formal counterpart of "any distinguishable framework factors
    through Raw."
  - §1.2 path corrections: `Research/NoDepthParity.lean` →
    `Hypervisor/Lens/Morphism/{NoDepthParity, DepthParityNotFold}.lean`;
    `notes/75_*, notes/76_*` → `research-notes/75_*, research-notes/76_*`
    (relocated, not deleted); current Lean counterpart
    `Hypervisor/Lens/SemanticAtom.lean`.
  - §7.1 updated: Lens-layer bleed migration (Recommendation 3) is
    deprioritized — `Raw.depth/leaves/fold_signed_swap/fold_swap_hom`
    remain in Firmware as acknowledged convenience leak.  Added
    Universal-Lens metatheory cross-reference.
  - §7.3, §7.4 obsoleted: `book/chapters/ch22_213.tex` and `book/AUDIT.md`
    no longer exist (`book/` retains only README.md; `papers/` retains
    only README.md after a02b751 deletion).
  - §9.4 updated: Paper 1 deletion noted; current Lean remnant of R1-R5
    motivation is `Meta/SelfRecognising.lean` (R1-R4 only); R1-R5 → ℂ
    chain not re-built post-deletion.  Universal-Lens / Atomicity story
    does not depend on it.
  - Companion architectural reference: `lean/E213/ARCHITECTURE.md`
    (canonical layer architecture, supersedes all earlier scattered
    layer-organization notes).

## Author & licence

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- 0 sorry, 0 external axioms.  Mathlib-free.
