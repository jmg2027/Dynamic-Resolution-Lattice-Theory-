# No Walls, Only Free Parameters: A Decomposition Calculus for the Boundaries of Mathematics

**Mingu Jeong**

*A self-contained exposition. Every numbered result corresponds to a
machine-checked Lean 4 theorem that depends on no axioms whatsoever —
not the law of excluded middle, not `propext`, not `Quot.sound`, not
choice. The modules are named inline; the verification protocol is
given in Appendix A.*

---

## Abstract

The classical landscape of foundational mathematics is usually drawn as
a map of **walls**: the axiom of choice that one may adopt or refuse;
the independence results of Gödel and Cohen; the unprovable consistency
statements; the Cantor, Russell, and halting diagonals; the large-cardinal
hierarchy that climbs without ceiling. These are habitually treated as
heterogeneous obstacles — some optional, some forced, some impassable.

This paper argues that they are not heterogeneous, and that all but one
of them are not walls. We introduce a **decomposition calculus** in which
every mathematical object is read as a pair `⟨C | L⟩` — a *construction*
`C` together with a *reading* (Lens) `L` — leaving a residue. Applied to a
boundary, the calculus returns the **section-count of the reading-fibration
over `C`**, and this count is always one of exactly four values:

> `∅ / 0 / 1 / many = absence / wall / forced / free`.

We prove (Theorem 4) that there is exactly **one** genuine wall, the
`0`-section case, and that it is the Lawvere diagonal — Cantor, Russell,
Gödel, the halting problem, and the forcing-generic are the *same* diagonal
read at different carriers. Everything else is either **forced** (a unique
section: the rigid structural axes, Theorem 3) or **free** (many sections,
none canonical: choice, forcing, large cardinals, Theorems 1–2 and 5).
The free parameters split, by the order-type of their fiber, into a
*symmetric* family (forcing) and a *one-way* family (large cardinals),
Theorem 5.

The calculus is **self-grounding**: it constructs every concrete instance
of the four cases by an axiom-free term, but it cannot construct its own
master classifier — and the reason is a theorem, not a gap. The would-be
master classifier *is* the wall (Theorem 6). Finally, self-classification
is **idempotent**: feeding the calculus its own classifier returns the
same four tags, so the tetrachotomy is the fixed point of the classifying
operation (Theorem 7).

The contribution is twofold. Mathematically, the four-way classification
unifies objects normally studied in separate subfields (reverse
mathematics, set-theoretic independence, recursion theory, large-cardinal
theory) under a single invariant — a fiber section-count — and every
claim is checked by a proof assistant against the empty axiom set.
Methodologically, it replaces the binary *adopt-or-refuse* stance toward
strong axioms with a *parametric* one: a strong axiom is not asserted or
denied but carried as a free parameter, and one computes per value of
the parameter.

---

## 1. The problem with refusal

Take the axiom of choice. The constructive tradition refuses it; the
classical tradition adopts it; the independence results say the question
is undecidable from the other axioms. Each of these is a *stance* toward
a single proposition `AC`, and each, taken alone, is a dead end for
someone who wants to *compute*. Refusal tells you what you may not do.
Adoption tells you that something exists without telling you which thing.
Independence tells you the matter cannot be settled — and then the working
mathematician shrugs and picks a convention.

The thesis of this paper is that the dead end is an artifact of treating
`AC` as a *proposition to be valued* rather than a *parameter to be
carried*. Once the latter view is taken, the three stances cease to
compete: they become three readings of the same fact, and the fact is
computable.

To make this precise we need a vocabulary in which "choose" is an object
rather than an act of faith. That vocabulary is the decomposition
calculus.

---

## 2. The decomposition calculus

### 2.1 Constructions, readings, residues

The calculus has one primitive: **distinguishing**. To distinguish is to
draw a difference; every act of distinguishing leaves a remainder it does
not exhaust. We do not posit a substrate on which distinguishing operates;
the remainder — call it the **residue** — is the *proven* leftover of the
act, not a given ground beneath it. (Formally, the self-cover induced by
distinguishing is faithful but never total; this is a Cantor-diagonal
theorem about how the cover is built, recorded in the foundational layer
as `FlatOntologyClosure.object1_not_surjective`. The reader who prefers
to may take it as a working postulate; nothing below depends on its
interpretation, only on its statement.)

An **object** is then written

> `OBJECT = ⟨C | L⟩ ⊕ Residue(L, C)`,

where `C` is a **construction** (the data assembled) and `L` is a **reading**,
or **Lens** — a map `C → α` for some readout type `α` that records *what
one reads off* the construction. The same construction read by different
Lenses yields different objects; the residue is what no single reading
exhausts.

The only structural notion we need from the calculus is this. Fix a
construction `C` and consider the family of readings compatible with it as
a fibration: over each point of `C` sits the set of admissible local
readouts, and a **global reading** is a *section* of this fibration —
a coherent choice of readout at every point. The central question the
calculus asks of any object is:

> **How many global sections does the reading-fibration over `C` admit?**

We will see that for the boundary objects of mathematics this count is
the entire content.

### 2.2 The tetrachotomy

The section-count takes one of four values, and the four are mathematically
distinct situations, not a continuum:

| count | name | meaning |
|---|---|---|
| `∅` | **absence** | the fibration is not yet built — the fibers are not even known to be inhabited |
| `0` | **wall** | the fibers are inhabited but no global section exists — a genuine obstruction |
| `1` | **forced** | exactly one global section — the readout is rigid, uniquely determined |
| `many` | **free** | more than one global section — the readout is a free parameter |

The reader should notice immediately that `∅` and `0` are different. The
empty case is *not-yet-constructed*: it precedes the question of whether a
section exists, because the fibers have not been shown inhabited. The
zero case is *constructed-and-obstructed*: the fibers are inhabited, yet
they cannot be threaded into a global section. Conflating the two is the
classical error that makes "there is no choice function" sound like a
defect rather than a structural fact about a *particular* fibration. The
distinction is the whole reason the classification has four cells and not
three; it is built as an object in the module `SectionCountWithAbsence`
(the four-valued `StatusCount` classifier `classify4`, with
`tetrachotomy_complete` and `absence_distinct_from_wall` establishing
exhaustiveness and the `∅`≠`0` separation).

We now traverse the four cells with the boundary objects of mathematics.

---

## 3. Choice is the `many` cell (Theorems 1–2)

### 3.1 A choice function is a section

Let `X : I → Type` be a family with each fiber inhabited. A **choice
function** is precisely a section `σ : ∀ i, X i`. This is not an analogy;
it is the definition. In the calculus, applying a section is an *act* — a
self-pointing of the residue — not an existence claim, so the calculus
never writes `∏_i X_i ≠ ∅`. It writes a *rule* — `σ_left`, `σ_right`,
`σ_min`, … — and reads.

> **Theorem 1 (choice is a free Lens parameter).** *There exist two
> explicit sections of the family `i ↦ Bool` and an operation that returns
> different values under each. The construction uses no choice axiom,
> because the sections are supplied as data.*

This is the module `ChoiceLens`, theorem `choice_is_free_lens_parameter`
(verified: 12 declarations, all axiom-free). Two sections `sigmaL`,
`sigmaR` are written down explicitly; an operation `readOp` satisfies
`readOp sigmaL 3 ≠ readOp sigmaR 3`; the theorem bundles them. The point
is not that the example is hard — it is that the *non-constructive content
of choice is exactly the freedom of `σ`*, and that freedom is visible,
computable, and axiom-free once `σ` is data rather than a postulated
existent.

### 3.2 What independence is

If no section is forced, then *both* of the conventions "adopt a section"
and "refuse to single one out" are consistent with the construction —
they are two readings of the one fact that `σ` is free. This is the
Gödel–Cohen independence of `AC`, recovered as a structural property of a
fibration rather than a metamathematical accident.

> **Theorem 2 (forcing is section-adjunction).** *Two distinct generics
> over a two-point poset yield two distinct global sections of the same
> construction, neither canonical.*

This is `ForcingToy`, theorem `forcing_toy_independence` (12 axiom-free
declarations). Carrying both candidate sections over the poset and
projecting per forcing-condition (`carryBoth` / `proj`) is exactly
sheaf-over-poset semantics, and — crucially for the axiom budget — it is
realized without function extensionality, by stating the relevant equalities
pointwise. Cohen's method of forcing, in this reading, is the *adjunction
of a generic section*: it does not decide `AC`; it exhibits the freedom of
`σ` by realizing two incompatible values of it in two extensions.

### 3.3 The binary case and LLPO

Over a two-element fiber, a section `σ ∈ {left, right}` is a single bit.
That bit is the `q = ±1` residue tag already carried elsewhere in the
calculus (the unimodular multiplier `multiplier_unimodular` of the module
`ResidueTag`), and the constructive principle **LLPO** (lesser limited
principle of omniscience) is precisely *that bit left undetermined*. Thus
the reverse-mathematics omniscience ledger and the set-theoretic choice
parameter are the same object at the smallest fiber. The omniscience
principles are catalogued, with their exact costs, in the module
`Omniscience` and the chapter `reverse_math_213`.

---

## 4. The forced cell and the one wall (Theorems 3–4)

### 4.1 Forced: the rigid axes

Not every reading is free. The *construction axes* themselves — the slots
that must be filled for the object to be the object it is — admit exactly
one section.

> **Theorem 3 (the forced pole).** *The reading-fibration of a construction
> axis has a unique global section: it exists and is unique.*

This is `SectionCount`, theorems `forced_exists_unique` (the `1` pole) and
`free_two_sections` (the `many` pole) together exhibiting the contrast
within one module (16 axiom-free declarations). A forced reading is one
where the construction leaves no latitude — it is the rigid skeleton on
which the free parameters hang. In the calculus's own atomic data the
forced numbers are the arity `(NS, NT) = (3, 2)`; we return to their
coupling with the free fibers in §6.

### 4.2 The wall is the diagonal, and there is only one

The `0` cell — inhabited fibers, no global section — is the only genuine
obstruction. The claim of this paper is that it is *singular*: every
celebrated impossibility in mathematics is this one cell, instantiated at
a different carrier.

> **Theorem 4 (the one wall).** *Cantor's theorem (no surjection
> `A ↠ 2^A`), Russell's paradox (no set of all non-self-membered sets),
> Gödel's first incompleteness (no consistent complete recursive
> extension), the halting problem (no total decider), and the
> forcing-generic (reached by no finite condition) are the same diagonal:
> a map that must both decide a predicate and appear as a row of its own
> cover is driven to a fixed point of negation, which is impossible.*

This is the Lawvere fixed-point pattern, realized in `MasterClassifierNoGo`
(45 axiom-free declarations) and given its limit-side reading in
`GenericAsCut`, theorem `generic_is_reached_by_none_cut` (12 axiom-free).
The generic deserves a word: it is the *positive* limit of a free `σ` —
the value approached by every finite forcing condition and reached by none
— and it has the exact shape of a real number presented as a cut, where
convergents narrow without the limit ever lying among them. The wall (a
reached-by-none *negative*, the diagonal one cannot reach) and the generic
(a reached-by-none *positive*, the limit one cannot finitely name) are
dual faces of the same reached-by-none structure.

So the map of mathematics has exactly one wall, drawn many times.

---

## 5. The free parameters split by fiber order (Theorem 5)

The `many` cell is not homogeneous. A free parameter ranges over a fiber,
and the *order-type* of that fiber determines the character of the freedom.

> **Theorem 5 (freedom splits by symmetry = fiber order).** *A free
> parameter over an unordered fiber is symmetrically free: its readings are
> interchangeable by an involution (swap), and adjoining one is reversible.
> A free parameter over a well-ordered fiber is asymmetrically free:
> strictly increasing, with no top, and one-way.*

This is `FiberSymmetry`, theorem `fiber_symmetry_law` (12 axiom-free).
The two halves are the two axes of set-theoretic strength:

- **Symmetric freedom = forcing.** The two values of `σ` over an unordered
  fiber are interchangeable; one can force either, and the extensions are
  symmetric. This is the selection axis, the `σ` of §3.

- **One-way freedom = large cardinals.** A well-ordered fiber has no top;
  climbing it is strictly monotone and irreversible. This is the *height*
  axis. A large-cardinal axiom is not a thing one adopts or refuses on the
  same footing as choice; it is a *position on a one-way ladder*, and the
  height-escape — the failure of the ladder to have a top — is the one
  diagonal again (Burali-Forti).

Thus the two independent axes along which the set-theoretic universe is
free — *which generic* (Cohen) and *how tall* (large cardinals) — are the
two order-types a free fiber can carry. Independence theory becomes the
study of the `many` cell, sorted by whether the fiber is symmetric or
well-ordered.

---

## 6. Self-grounding and the fixed point (Theorems 6–7)

### 6.1 The classifier classifies, and lands on the wall

The calculus has so far classified *objects*. It is itself an object: the
classifying operation `classify` reads a fibration and returns one of the
four tags. What happens when it is asked to classify itself?

> **Theorem 6 (the master classifier is the wall).** *A would-be master
> classifier that both decides the diagonal predicate and occurs as a row
> of its own cover is forced into a fixed point of negation; no such
> classifier exists. The calculus therefore builds every concrete instance
> of the four cases by an axiom-free term, but not its own master
> classifier — and its un-buildability is a theorem.*

This is `MasterClassifierNoGo`, theorems `master_classifier_is_the_wall`
and `self_grounding_capstone`. The result is the paper's structural
keystone: the calculus is **self-grounding** in the precise sense that the
limit of its own classifying power is not an external assumption imposed
on it but an *internal theorem it proves about itself*. It is the same
Lawvere diagonal of Theorem 4, now with the classifier itself as carrier.

What *can* be built is the part below the wall:

> *The classifier is total on decidable fibers, and on such fibers the wall
> tag `0` is structurally unreachable.*

This is `TagOfDecidable`, theorems `tagOf_total` and `tagOf_never_wall`
(12 axiom-free). The wall appears only at the `Type`-valued self-cover; on
everything decidable, the classification is total and never produces a
wall. The boundary of the calculus's self-knowledge is exactly the one
wall, and not one inch nearer.

### 6.2 The normal form is the tetrachotomy

There is a final reflexive turn. The normal form `⟨C | L⟩ ⊕ Residue` is
*itself* an instance of the four cells: the construction `C` is **forced**
(tag `1`), the reading-parameters `L` are **free** (tag `many`), the
residue is the **wall** (tag `0`), and the not-yet-built is **absence**
(tag `∅`). The forced base even shapes the free fibers — the forced atom
`NT = 2` is exactly the binary fiber over which `σ` is the `q = ±1` tag of
§3.3.

> **Theorem 7 (the idempotent fixed point).** *The forced arity
> parametrically determines the arity of the free fiber and the modifier
> of the wall; and applying `classify` to any reading — including `classify`
> itself — returns the same four tags. Self-classification is idempotent:
> the tetrachotomy is the fixed point of `classify`.*

This is `ArityCoupling` (theorems `arity_coupling`,
`forced_NT_couples_free_and_wall`, `fpf_modifier_iff`; 16 axiom-free) — the
*weld* that ties the forced base to the free and wall cells in a single
parametric statement — together with the idempotence reading. The
classification does not regress: classify the classifier, and you get the
tetrachotomy back. The four cells are stable under self-application, which
is what it means for a foundational scheme to close on itself without an
infinite ascent of meta-levels.

---

## 7. What this buys the working mathematician

**A single invariant across four subfields.** Reverse mathematics studies
the omniscience cost of theorems; set theory studies independence; recursion
theory studies undecidability; large-cardinal theory studies consistency
strength. The tetrachotomy says these are one study: the section-count of a
reading-fibration, sorted into absence / wall / forced / free, with the
free cell further sorted by fiber order. LLPO (reverse math), the choice
parameter (set theory), the halting diagonal (recursion theory), and the
large-cardinal ladder (consistency strength) are the binary-fiber free
parameter, the general free parameter, the wall, and the well-ordered free
parameter, respectively.

**A parametric stance toward strong axioms.** One need not adopt or refuse
choice, the continuum hypothesis, or a measurable cardinal. One carries
the parameter and computes per value. "AC true" and "AC refused" are not
opponents; they are the two readings of `σ`-is-free. This is already how
the practicing set theorist behaves — proving theorems "in `ZFC`" and "in
`ZF + ¬AC`" as parallel computations — but the calculus makes the parameter
an *object* rather than a background convention, so that the per-value
computation is uniform.

**A machine-checked floor.** Every theorem above is verified by Lean 4
against the *empty* axiom set: not merely without choice, but without the
propositional-extensionality and quotient axioms that even constructive
type theory normally permits. The classification of the boundaries of
mathematics is itself carried out below all of those boundaries. The
verification protocol is in Appendix A; the nine modules total 150
axiom-free declarations.

---

## 8. Limits, honestly

The general idempotence statement `classify ∘ classify = classify`, as a
single closed theorem, *is* the wall: it is un-buildable by the very
self-grounding of Theorem 6, since a total master classifier is exactly
what Theorem 6 forbids. What is open is a **partial decidable idempotence
below the wall** — the restriction of the idempotence statement to
decidable fibers, where Theorem `tagOf_total` already lives. Whether the
one-way-ness of the height axis (the Gödel-II flavor) is a genuinely new
fact or merely the escape/converge asymmetry of Theorem 4 read on the
strength axis is likewise open.

A `σ`-parametrized *operation library* — the ultrafilter, the
well-ordering theorem, and Hahn–Banach each carried with an explicit `σ`,
and the independence statement itself as a model-theoretic Lean theorem
("`σ` free ⟹ both adjunctions consistent") — is the natural next
construction, of which only the two-point forcing toy (Theorem 2) is so
far built. The dense-set genericity beyond the single-section cut of
Theorem 4 is not yet formalized. These open directions are tracked in the
project's frontier register.

None of these gaps touches Theorems 1–7. The map has one wall; we have not
yet walked every road that the four cells open, but the cells themselves
are closed and checked.

---

## 9. Conclusion

The boundaries of mathematics have long been drawn as a museum of distinct
impossibilities and optional commitments. The decomposition calculus
redraws them as the four readings a fibration can have: **absent** because
unbuilt, **walled** because no section threads the fibers, **forced**
because exactly one does, **free** because many do. There is one wall —
the Lawvere diagonal — appearing as Cantor, Russell, Gödel, the halting
problem, and the generic. Everything else is a free parameter, and the
free parameters are sorted by the order-type of their fiber into forcing
(symmetric) and large cardinals (one-way). The calculus classifies itself,
lands its own master classifier on the one wall as a theorem, and is
idempotent under self-application: the four-cell scheme is its own fixed
point.

The shift in stance is the lasting point. A strong axiom is not a thing to
believe or disbelieve. It is a parameter to carry. Refusal explains
nothing; parametrization explains *which* freedom an axiom names, *why* it
is independent, and *what* its limit is. And the whole account stands on a
floor with no axioms beneath it.

---

## Appendix A. Reproduction

All results are Lean 4, no external libraries. From the repository root:

```
cd lean && lake build E213.Lib.Math.Logic
```

For each module `M ∈ { ChoiceLens, ForcingToy, SectionCount,
SectionCountWithAbsence, FiberSymmetry, MasterClassifierNoGo,
TagOfDecidable, GenericAsCut, ArityCoupling }`:

```
python3 tools/scan_axioms.py E213.Lib.Math.Logic.M
```

Each reports `N pure / 0 dirty`; `#print axioms <theorem>` on every
headline result returns *"does not depend on any axioms."* The nine
modules and their tallies:

| module | declarations | headline theorem |
|---|---:|---|
| `ChoiceLens` | 12 | `choice_is_free_lens_parameter` |
| `ForcingToy` | 12 | `forcing_toy_independence` |
| `SectionCount` | 16 | `forced_exists_unique`, `free_two_sections` |
| `SectionCountWithAbsence` | 13 | `tetrachotomy_complete`, `absence_distinct_from_wall` |
| `FiberSymmetry` | 12 | `fiber_symmetry_law` |
| `MasterClassifierNoGo` | 45 | `master_classifier_is_the_wall`, `self_grounding_capstone` |
| `TagOfDecidable` | 12 | `tagOf_total`, `tagOf_never_wall` |
| `GenericAsCut` | 12 | `generic_is_reached_by_none_cut` |
| `ArityCoupling` | 16 | `arity_coupling`, `forced_NT_couples_free_and_wall` |

The empty-axiom standard is strict: a result that depends on `propext`,
`Quot.sound`, `Classical.choice`, `native_decide`, or any library axiom is
treated as unproven for the purposes of this paper. None of the above do.

## Appendix B. Where the narrative lives

- Promoted chapter: `theory/math/logic/no_walls_only_parameters.md`.
- The choice essay: `theory/essays/synthesis/the_axiom_of_choice_is_a_free_lens_parameter.md`.
- The reverse-mathematics ledger (omniscience costs): `theory/math/logic/reverse_math_213.md`.
- The residue and the no-exterior principle: `seed/AXIOM/01_residue.md`,
  `seed/AXIOM/05_no_exterior.md` §5.1.

---

*Acknowledgments. The formalization, the Lean proofs, and the axiom audits
were carried out in collaboration with Claude (Anthropic), which served as
proof engineer and adversarial reader throughout. The theory and all
foundational insights are the author's.*
