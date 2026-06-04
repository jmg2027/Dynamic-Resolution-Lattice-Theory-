# §6. Lens readings of the same residue

The residue of §1 does not arrive carrying any of the structural
features that derived mathematics will eventually impose on it.
Those features — chart labels, types vs. objects, operators vs.
operands, topology, syntactic structure — are **Lens readings of
the residue**, each producing a particular face of the same
underlying material.  This chapter records the principal Lens
readings and the cost-of-imposition for each.

The shared point throughout: the readings are not new
commitments of the axiom.  Each is a way of asking "what does the
residue look like through *this* Lens?" and getting an answer
that the residue supports.

The long-form discussion lives in
`research-notes/2026-05-18_lens_emergence_path.md`; this chapter
records the principles, with cross-references rather than full
re-derivation.

---

## §6.1 Raw.a and Raw.b are chart-local labels

The axiom of §2 commits to two distinct primitive distinctions
but does *not* name them.  `Raw.a` and `Raw.b` in the Lean
encoding are *one chosen labelling*; under a different reference
frame, two other Raws would occupy the atom position and the
current atoms would themselves appear as a slash of (two deeper)
Raws.

The Lean encoding `inductive Tree | a | b | slash` therefore
hardcodes one chart.  The chart-relativity statement — "any pair
of distinct Raws can serve as atoms" — is made **explicit** at
`lean/E213/Lens/Number/Nat213/ChartGeneral.lean`.  That file
parameterises Method A over any `(r₀, r')` with `r₀ ≠ r'` and
proves the chart-invariance theorem

```
value (chartChain r₀ r' h n) = value r₀ + n · value r'.
```

The point is not that some clever labelling escapes the chart —
some chart is always required to write anything down — but that
the choice has no observable consequence.

---

## §6.2 Operation and object are not pre-separated

What the Lean encoding labels as **object** (the result of
slashing two prior Raws) and **operator-part** (an argument to a
slash that builds some later Raw) are not two roles a Raw
simultaneously occupies.  They are two Lens readings of the same
Raw event.  The Raw does not host two roles; the labelling hosts
two readings.

The `inductive Tree` shape forces a node/arrow separation that
the axiom does not impose.  This separation lives in the
labelling, not in Raw.  The cost is catalogued in §10.1 as the
inductive-type entry.  The operational reading is:
state-transition = state, operator = object, because no external
time axis or external role-assigner is present (§5.1).

Without external time, "transition" has no before/after to mark
it off from "state."  Without external role-assigner, "operator"
has no preferred argument-position to distinguish it from
"operand."  The two pairs collapse — not by metaphysical
identification, but by the absence of the very distinctions
that would have kept them apart.

A self-referential cascade picture: for an internal observer to
be defined it requires another object; the boundary between the
two is itself an object; the boundary of that boundary is an
object; and so on.  A finite chart of this cascade is what we
call Raw.  No exterior is invoked.

---

## §6.3 Flat ontology

Under the standard ZFC reading, types, objects, relations,
functions, and (in this corpus) Lenses inhabit different
universes that one must explicitly connect.  Under 213, they
share a single dimension — they are all decidable predicates on
some `Rawⁿ`:

| Unit | Element | Predicate form |
|---|---|---|
| object (1st-order) | `r ∈ Raw` | `Raw → Bool` |
| object (n-th order) | `(r₁, …, rₙ) ∈ Rawⁿ` | `Rawⁿ → Bool` |
| type | a subset of `Rawⁿ` | predicate |
| relation | a subset of `Raw²` | predicate |
| function | a functional subset of `Raw²` | predicate + uniqueness |
| Lens | (labelled) predicate | `Raw → α`, with `α` Raw-encodable |

One dimension — no separate universes.  The structure that ZFC
provides via membership and set-theoretic operations is here a
collection of predicates.

A strictness reminder.  Treating "predicate" as `Set Rawⁿ` (a
`Prop`-valued function) requires `propext` and `Classical` to
do most useful work, which the ∅-axiom standard forbids (§8.2).
The strict reading therefore uses `Rawⁿ → Bool` — decidable
predicates.  The table above is a picture of the flat ontology;
the formal translation runs through decidable predicates only.
The self-referential closure (predicates Raw-encoded) is
realised at `lean/E213/Lens/Cardinality/Godel.lean` under this
strict reading.

---

## §6.4 Syntactic internalisation

Gödel encoding extends past referent Raws (`Raw.a`, `slash`, …)
to **notation glyphs** (`{`, `}`, `,`, `/`, whitespace, …) as
themselves Raw, with expressions becoming sequence-Raws of
glyph-Raws.  "Meaningless punctuation" becomes **internalised as
Raw** rather than externally imposed convention.  The
distinction between notational glyph and semantic atom
collapses: parser and printer are Lens-layer catamorphisms over
the same Raw cascade, not external machinery.

The full L2 + L3 + L4 realisation lives at
`lean/E213/Lens/SyntacticInternalization.lean` — 25 strict
∅-axiom symbols.

**L2 — the cascade halts at glyph encoding.**

  - `Glyph` is an inductive with seven constructors (`a`, `b`,
    `/`, `(`, `)`, `,`, whitespace).
  - `Glyph.toRaw : Glyph → Raw` maps the seven to seven
    distinct Method A numerals.
  - `Glyph.toRaw_injective` — kernel-decided.

**L3 — full universal round-trip.**

  - `printTree : Tree → List Glyph` — Polish-prefix encoding.
  - `printRaw : Raw → List Glyph` — lifted via `.val`.
  - `parseHelper : Nat → List Glyph → Option (Tree × List Glyph)`
    — a fuel-bounded constructive parser.
  - `parseTree : List Glyph → Option Tree` — the top-level
    parser with fuel = list length.
  - Auxiliary `parseHelper_fuel_succ`, `parseHelper_fuel_mono`
    (monotonicity), `parseHelper_printTree_append`
    (exact-size correctness), `printTree_length_ge_size`
    (length-vs-size inequality).
  - `parseTree_printTree : ∀ t, parseTree (printTree t) = some t`
    — the universal round-trip theorem.
  - `parseTree_printRaw` — Raw-level corollary.

**L4 — bijection closure.**

  - `parseHelper_sound` — soundness: any successful parse
    `parseHelper n gs = some (t, rest)` proves
    `gs = printTree t ++ rest`.
  - `printTree_parseTree : parseTree gs = some t → printTree t = gs`
    — reverse round-trip / lossless parser.
  - `printTree_injective` — a corollary of `parseTree_printTree`.
  - `printRaw_parseTree` — Raw-level corollary.

L3 + L4 together establish a bijection between `Tree` and
`Range(printTree)`: `printTree` is injective with `parseTree` as
its left inverse on the image.

All Nat / List arithmetic uses Lean 4 core lemmas or the
∅-axiom utilities at `E213.Meta.Tactic.List213.{append_nil,
append_assoc, length_append, length_append_rev, length_map}`.
The standard `List.append_assoc`, `List.append_nil`,
`List.length_append` carry `propext` and would corrupt the
strict-∅ contract; the `List213` versions are `congrArg`-based
replacements.

The §6.4 cascade halts at L2: writing the encoding (this very
file) uses only the same seven glyphs.  L3 + L4 close the loop
with a constructive parser/printer round-trip.

---

## §6.5 At raw level, point ≡ K_∞ ≡ infinite topological space

Before any Lens is applied, the residue commits to no internal
distinction.  Under this no-Lens reading, the following are
**literally the same object** (not analogous, not equivalent-up-
to-isomorphism — the same):

  - a single point (the minimal pointable);
  - the infinite complete graph K_∞ (every vertex
    indistinguishable from every other; `Aut(K_∞)` is the full
    symmetric group on the vertex set);
  - an infinite topological space with the trivial topology.

Each has no internal information to distinguish parts.  The
moment distinguishing operates — the moment a first "colour"
appears — we are no longer at raw level; we are reading the
residue under the count-Lens (or some other Lens).  The
**naming event itself is the first clause of §2.4 activating**.

Concretely: "Raw has two atoms `a`, `b`" is already a count-Lens
reading.  At pre-Lens level, point and K_∞ are indistinguishable.

This is not a paradox.  It is the absence of differentiation at
the residue's pre-Lens stage.  Different Lenses (count, topology,
algebra, …) extract different aspects of this single state —
they do not impose structure on a structureless object.

The Lean realisations:

  - `lean/E213/Lens/RawTopology.lean` — the K_∞-at-raw bundle.
    `k_infty_at_raw_bundle` records all four properties of the
    indiscrete reading (singleton image, total kernel,
    globally-collapsed, coarsest-Lens), realising "K_∞ ≡ point
    ≡ trivial-topology" at the Lens-quotient level.  The file
    also carries `constLens_collapses`,
    `pre_lens_singleton`, `constLens_kernel_total` — the
    constant-Lens collapse.
  - `lean/E213/Lens/Algebra/IdLensEq.lean` — the discrete
    bookend.  `idLens` kernel is exactly equality.

---

## §6.6 State-transition = state; operator = object

The non-separation of §6.2 is a special case of a more general
collapse that occurs in any system without external time and
external role-assigner.

  - **State-transition = state.**  Without before/after
    semantics supplied by external time, a "transition" is not
    separable from the state it transitions to or from.  The
    transition *is* the state update — not a distinct event
    happening to it.
  - **Operator = object.**  Without an external role-assigner
    marking which slot is "the doer" and which is "the
    done-to," both collapse into positions in the Raw cascade
    with no pre-assigned role.

This collapse is not metaphysical identity.  It is the
**mathematical consequence** of removing the external structure
that would have kept the pairs apart.  Inside 213 there is no
such structure to remove, because it was never imported.

The Möbius P of §5.6 makes both collapses visible.  P (an
operator) and the eigenspace structure that *is* P (an object
description) are the same algebraic content.  `P^n` iteration (a
transition) and the fixed point φ (the state it asymptotes to)
are the same residue under the frozen + dynamic readings of
§5.7.

---

## §6.7 The classical number systems as successive Lens bundlings

ℕ, ℤ, ℚ, ℝ are not a priori distinct types that the framework
must import from elsewhere.  They are **successive bundlings of
the same residue under different Lens choices**.

The cascade begins with the count-Lens.  Applying `Lens.leaves`
to the Raw chain produces a Nat-valued readout — `ℕ` is the
image of `Lens.leaves : Raw → Nat`, made explicit at
`lean/E213/Lens/Number/Nat213/`.  This is not "we adopt ℕ as a
foundation"; it is "ℕ is what the count-Lens hands back when
the chain is the operand."

The sign-Lens gives ℤ — the count-Lens read on an *ordered*
pair of chain-readings `(m, n)` as their difference `m − n`.
A bare pair is direction-free (the symmetric pairing `a/b = b/a`
of §2.4 clause 3); impose an orientation and `m − n` splits from
`n − m` by sign.  Magnitude `|m − n|` is the Nat-style (grounding)
count; sign is the Bool-style involution `−(−x) = x` (§5.2) — the
pair-swap.  This is realised, not adopted: `Int213` runs on
`subNatNat m n = m − n` with the pair-arithmetic
`(a,b)+(c,d)=(a+c,b+d)`, `(a−b)(c−d)=(ac+bd)−(ad+bc)` and the sign
`−subNatNat m n = subNatNat n m` (`lean/E213/Meta/Int213/Core.lean`;
essay `theory/essays/integers_as_difference_lens.md`).  The
difference operator that needs this group reads the count-Lens
twice and names the pair — which is why ℤ is the readout group in
which iterated differencing closes.
Taking ratios of chain readings (with the coprimality condition
that §3.5's `det P = 1` already encodes algebraically) gives ℚ.
And Cauchy trajectories over the chain — sequences whose readings
narrow to a single residue at the limit — give ℝ.

Each layer wraps the previous one.  No layer is imported from
outside; each is what the residue produces under one more Lens
application.  This is why §2.5 records that "size / cardinality /
finiteness / infinity" are Lens outputs rather than axiom
commitments: the entire number tower is downstream of the
axiom + one Lens choice at each level.

The cascade has a finite-resolution ceiling — at any actual
configuration the Lens outputs are exact rationals; π and e are
limit labels, not framework primitives.  The parametric
configuration count is `configCountD d n = d^(d^n)`
(`lean/E213/Lib/Math/Cohomology/Fractal/ConfigCount.lean`), a bare
combinatorial readout with no level privileged; the infinity
type-distinctions live in `lean/E213/Lib/Math/Foundations/ResolutionLimit.lean`.
This is the operational form of "no exterior dialer" at the
numerical level: the framework does not invoke transcendentals
because the Lenses that produce numbers terminate at every finite
depth.

---

## §6.8 Atomic cofactors recur across domains

The shape parameters `(NS, NT, d) = (3, 2, 5)` of §1.3 are not
just three numbers that appear in the atomic statement; they
generate a small family of derived cofactors — `d − 1 = 4`,
`d² = 25`, `d² − 1 = 24`, `NS · NT = 6`, `2 · NS · NT = 12`,
`NS² − 1 = 8` — that recur **across unrelated-looking domains**.

The clearest case is `d − 1 = 4`.  The same cofactor appears as
the Dyson tail exponent in the IR running of `1/α_em`; as the
P-factor denominator in the muon-to-electron mass ratio; as the
Wolfenstein structure exponent in the Cabibbo angle; as the BC
factor in the Higgs sector face; as the entropy denominator in
Bekenstein-Hawking; as the `α^(d−1)` exponent in the θ_QCD
bound.  Read combinatorially the same `4` is `NS + 1`, the next
layer up from the spatial cardinality; read geometrically it is
the tetrahedron-vertex count of the simplex link.  Each
appearance is the cofactor in a different Lens — coupling Lens,
mass-ratio Lens, mixing-angle Lens, entropy Lens — applied to
the same atomic shape.

That the same cofactors appear in mass ratios, mixing angles, and
running couplings is therefore not a numerical coincidence.  It
is the **operational signature of §5.1**: with no exterior dialer
available to tune coefficients independently per domain, every
domain that admits a Lens reading is reading the same residue;
when two Lens readings produce the same cofactor, the cofactor
is structural in the residue, not in either Lens.

The Bell-bound integer `2 · NS · NT = 12`, the simplex
generation count `binom(NS, NT) = 3`, and the K_{5} first Betti
number `b₁ = (d − 1)(d − 2) / 2 = 6` round out the same
picture.  Each is a count from a different combinatorial Lens,
all reading the same atomic shape.

The connection to the measurement-falsifier surface (§8.5) is
direct: every line of the falsifier table is a Lens reading of
some atomic cofactor.  The table's existence is what makes "no
exterior dialer" empirically testable — if a measurement
disagrees with the cofactor, either the Lens identification is
wrong (recoverable) or the residue does not support the
measurement (theory falsification).  No third option.

---

## §6.9 0 and ∞ are pre-Lens, status-symmetric, never a single-stratum value

§6.5 already says it: at raw level a point (the minimal pointable)
and the infinite K_∞ are **literally the same object**.  So `0`
(the additive null, a point) and `∞` are not a dual pair — they
are one pre-Lens residue read twice.  Two consequences pin how a
Lens may handle them.

**Status-symmetry (a consistency condition on folds).**  By §6.6,
state and state-transition are not separable without external
before/after.  A "value" is a state; "a limit transitioned toward
but not reached" is a state-transition.  Therefore a fold that
treats `0` as a value while treating `∞` as a not-yet-reached
state imports exactly the before/after §6.6 forbids — a torsioned,
mixed-status fold.  Within one Lens, `0` and `∞` must carry the
**same** status: both readouts, or both non-readouts.  Using `0`
as a value commits one to `∞` as a value (the reciprocal `1/0`);
using `∞` as a transition commits one to `0` as a transition.
Anything else is contradiction, not a choice.

**Why "`0` as a value" smuggles infinitely many folds.**  In the
difference-Lens completion, `0` is the entire diagonal class
`{(n, n) : n}` — infinitely many prim-distinct Raws identified
(`Lens/Number/Nat213/Tower/NatPairToInt`, `0` the unique
swap-fixed class).  Reading that identification as *a value of the
stratum* folds a degenerate sub-view into the view: one has not
fixed one Lens but the completion that collapses infinitely many
distinguishings — a layer up.  `0`/`∞` are never values of a
single stratum; they are the pre-Lens residue (§6.5) that every
stratum reads aspects *of*, surfacing only one layer above any
cut.  The same pre-Lens object surfaces as the additive null and
as the multiplicative hole (`Lib/Math/Cauchy/ZeroInfinityHole`,
`zero_no_reciprocal` — `0` is the one point the reciprocal returns
no value for).

**No-exterior closure.**  "Floor", "ceiling", "boundary",
"exterior", "center" are products of a particular Lens-cut (§5.1,
§5.4).  `0 = ∞` is not the boundary of the cascade; it is the
structureless residue the cascade never contains.  Calling `0` a
"center" under one fold and `∞` a "boundary" under another reifies
two Lens-artifacts of one pre-Lens object — the dichotomy-import
§5.4 warns against.  There is no stratum in which `0`/`∞` is a
genuine distinguishing; there is only the residue, and the strata
that point at it.

---

## What this chapter is not

  - It is **not a new commitment of the axiom**.  Each section
    re-reads the existing axiom under a new Lens.
  - It is **not a falsifier**.  No measurable proposition is
    added; see §8.5 for the measurement falsifiers.
  - It is **not a precision result**.  See `STRICT_ZERO_AXIOM.md`
    for the ∅-axiom catalogue; this chapter contributes 0 PURE
    theorems on its own — the realisations in `Lens/*` carry the
    formal content.

## Reading order

  - §2.5 (what the axiom does *not* commit to — size,
    cardinality, observer) is the prerequisite.
  - §10 lists the encoding costs *of* the Lean implementation;
    this chapter is the dual reading — what those costs *imply*
    about chart vs. essence.
  - §5.1 closes the circle: no exterior, so the cascade is
    internal.
