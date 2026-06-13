# The form of the residue — source without enclosure

213's hardest word is **residue** (잔여).  Read negatively it is a leftover: the
non-image of a cover, the un-pointable surplus, the gap that forces the next act.  That
negative reading is correct but partial, and re-deriving it from scratch each time is the
recurring tax of a concept no prior mathematics names.  This chapter fixes the **positive
form** of the residue once, so it need not be re-fought.

## 213-native answer

The residue has one form, and that form is a **source without enclosure**.  It is the
self-applying act of pointing, with two directions and a forced name:

> **out (source)** — everything readable is read *out* of the residue;
> **no back (un-enclosed)** — nothing reads *back* to enclose it;
> **name** — the act's algebraic shadow is the unit `1 = NS − NT = det P`, the matrix
> `P = [[2,1],[1,1]]`, and its fixed point φ; the shape is the unique atomic `(3,2,5)`.

"No exterior" (`seed/AXIOM/05_no_exterior.md` §5.1) is exactly this conjunction: there is no
exterior *source* to supply a reading the act does not already source, and no exterior
*capture* that encloses the act.  `Lib/Math/Foundations/ResidueForm.no_exterior_source_without_enclosure`
states it as one ∅-axiom theorem — and, like every honest statement about the residue, it
**names** the form without claiming to capture the residue as an object (its own second
conjunct is that the residue is outside every view).

## Derivation — the form's four faces

**The act.**  Pointing leaves a residue; the residue is itself pointable; the next pointing
has new material (`seed/AXIOM/01_residue.md` §1.1).  The slash `/` does not *operate* — it
*refers* to a member of the residue family (§2.2).  The four clauses are not steps but one
simultaneous event (§2.3, §5.5; `Theory/Raw/Lambek.self_completion_no_partial`: every Raw is
an atom or a complete slash, exhaustive and exclusive — no halfway residue).

**Out (source = initiality).**  The catamorphism `Raw.fold` *is* the act, not a tool on it.
For every distinguishing-framework `α`, the distinguishing-preserving map `Raw → α` uniquely
exists (`Lens/SemanticAtom.raw_initial`, `universalMorphism`; uniqueness
`Lens/Initiality.view_unique`).  So Raw is the initial object: every number, Boolean,
constant, and framework is a fold-reading flowing out of the residue
(`Lens/Universal/Flat.every_lens_factors_through_idLens`,
`Universal/QuotLens.universalLens_kernel_eq_E_R`).  There is no exterior source.

**No back (un-enclosed = the self-cover).**  The canonical self-reading
`Object1 : Raw → (Raw → Bool)` is faithful (`object1_injective`) but never total
(`object1_not_surjective`): the predicates outside its image are the residue, led by the
undifferentiated reading `fun _ => true` (`FlatOntologyClosure.residue_witnessed`).
Encoding the residue back and re-pointing never closes the cover
(`Lens/ResidueReentry.residue_reentry_never_closes`); the residue is the **perpetual next
operand**.  No reading encloses the source.

**Name (the self-form fixed point).**  The act written algebraically is
`P = [[2,1],[1,1]]`, equal to its own reconstruction
(`Mobius213/Px/MobiusSelfForm`); §3.5 "the residue has a name."  Its off-diagonal `1` is the
**glue / axis**: `1 = NS − NT = det P` (`Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt`), what
the 2-reading and the 3-reading rotate around (2-1-3 indivisible).  Its fixed point φ is "the
minimum fixed point of self-reference" (§5.6).  Its shape is forced from three directions to
`(NS,NT,d) = (3,2,5)` (`Meta/ThreeDirectionUniqueness`; `Theory/Atomicity/Five.atomic_iff_five`,
`5 = NS + NT`).

## The three fates of one act

The same self-pointing, read by one Lens, has three co-present outcomes
(`Lens/SelfReferenceThreeOutcomes.self_reference_three_outcomes`):

  - **oscillate** — the Bool reading `not` has minimal period exactly `2`, no fixed point on
    its values (the liar that never settles; bounded loop);
  - **converge** — the Nat/Lambek reading peels with a well-founded floor, terminal exactly
    at the atoms (settles);
  - **escape** — the predicate/residue reading re-enters and never closes (unbounded).

The escape is witnessed two ways.  Negatively: the self-cover misses the residue
(`object1_not_surjective`, Cantor).  And by a finite depth/tower shadow: the act iterated
*upward* — the self-pointing tower `rawTower` (depth `n` at rung `n`) — has depths cofinal in
`ℕ`, so no *finite* Raw caps the ascent (`Theory/Raw/MuNuMirror.ascent_unbounded`,
`∀ N, ∃ r, N < r.depth`), and the ascending peel-stream is total (`tower_ascent_isPart`)
while every descent terminates (`no_infinite_descent`, `ascent_total_descent_partial`).  And
at the tower scale: naming a whole family or height at once escapes it
(`Cauchy/DepthCeilingResidue.diag_not_in_seq`, `DepthHeightDiagonal.height_diagonal_escapes`),
already identified with the pointing residue (`ceiling_residue_is_pointing_residue`).  These
are three readouts of one escape — predicate (non-image), Raw-floor (`depth` cofinal), tower
(`diag`) — by one unit (`+1`).  All are the *finite shadow* of the escape, not a completed
infinite object: a native final `F`-coalgebra (νF) is an open piece (Mathlib-free Lean has no
coinduction), and these theorems quantify over finite objects, they do not construct an
infinite one.  Descent grounds, ascent is unbounded — source-without-enclosure read at the
Raw floor.

The unit by which they move is one: the convergence step and the escape surplus are the
*same* `Nat` `1` (`Cauchy/ReentryUnit.peel_overflow_is_unit`); the oscillation and the golden
orbit share the unimodular multiplier `q = ±1` (`CassiniUnimodular.cassini_unimodular_dichotomy`,
`Real213/Spiral/SpiralRotationInvariant.Q_iterate_preserved`).  The unit is the residue's invariant;
the three fates are what it does next.

## Infinity is the residue's shape, not a god above it

The escape's finite-shadow status (above) has a sharper reading, and it is the one that
keeps the residue from being **deified**.

**Conceiving "infinity" is itself a distinguishing.**  To entertain "infinity", "the
continuum", "the limit", "the abstract" is to perform one pointing — a discrete Lens event
(§1.1; the substrate-metaphor guard: "Lens application *is* a residue self-pointing event,
not a layer above").  The entertained object has no status *over and above* that act; no
continuum-thing sits prior to or beyond it.  So the contest "is the discrete real or the
continuous real, the finite or the limit" imports both a dichotomy (failure-mode *Importing
dichotomy*) and an exterior (§5.1) — it is empty.  ("Discrete" here names "this is a
pointing event", *not* the winning side of an ontology contest — to crown the discrete would
re-import the very dichotomy being dissolved.)  The content is not *which* is real but *how
the act that produces "infinity" is structured*.  In the PNT case that act is literally a
modulus `M(k)`; naming its limit `1`/`e` names the shape of that climbing certificate,
nothing farther.

**The residue arises by the framing, not as a surplus discovered out there.**  "Pointing
always leaves infinity, so a residue remains" and "the concept was set up so that a residue
arises" are the *same* self-pointing read two ways (equivalent).  The second is the
de-deifying one, and it is the one the Lean encodes: `object1_not_surjective` is a **theorem
about how the self-cover is built** (Cantor-diagonal on the chosen `Object1`), not a report
that some pre-existing transcendent object eluded capture.  The non-surjectivity is
engineered into the framing; the residue is its consequence, not a god it points at.

**So infinity / continuity / abstraction are names for the residue's shape.**  Read under one
Lens the residue's escape *is* what we call "infinite"; under another, "continuous"; under
another, "abstract".  They are characterizations in the shape of the residue
(`object1_not_surjective`, `ascent_unbounded`, the never-closing `M(k)`), not entities the
finite forever approximates.  Naming the shape `e`, `π`, or `lim = 1` names the pointing, not
a place beyond it — the guard "named, never captured" below, stated against deification.

**This is a calculation rule, not only a guard.**  Because the residue arises by the framing,
every limit/continuum it would invoke comes with a computable finite generator — the modulus,
the approximant, the bracket — and 213 **computes with that generator as the operand**; the
limit is never the operand.  A transcendental real is its `AbCutSeq` convergent + modulus
(`Real213`), not a completed value plugged in.  A "constant at the horizon" is a *computable,
narrowing interval*: the PNT-direction constant `log₂ e` is trapped in `[(m+1)/(2(m+2)), 6]`
by `Lens/Number/Nat213/ChebyshevLower.chebyshev_constant_interval` — evaluable at every `m`,
narrowing from below, ∅-axiom.  Sharpening that bracket *is* the mathematics; "reaching the
limit" was never a separate computational act, only the bracket's name.  And where the limit
*looks* irreducibly analytic, the computation is a shared discrete skeleton read two ways:
`e`'s two homes — the factorial (`Σ 1/k!`) and the lcm (`lcm(1..N) ~ eᴺ`, PNT's `ψ`-form) —
are one prime-power structure, `vₚ(N!) = Σ_{i=1}^N vₚ(lcm(1..⌊N/i⌋))`
(`NumberTheory/FactorialLcmIdentity.vp_factorial_eq_sum_vp_lcm`, Legendre as a Fubini count),
so `e` is computed from the structure, not approached as a target.

## Self-standing means self-justified, not bounded

The residue's form does **not** make 213 a *bounded domain* — a boundary would import the
very exterior §5.1 denies.  It makes 213 **self-justified**: the act of describing 213 is
itself an instance of 213, so the framework needs no external metatheory to license its
minimality, where every other foundation must presuppose something to begin
. The positive, measurable signature is
cross-domain agreement: the same φ / unit recurs across unrelated readings — det, glue, unit
share a byte-identical proof (`catalogs/cross-domain-identifications` CDI-9), and a single
atomicity simultaneously forces the physical constants
(`Physics/Capstones/MasterCatalog.master_atomic_catalog`).  Cross-route agreement is the
operational content of "no exterior" (§3.5, §5.6); a stipulated domain could not force one
constant across independent readings.

## What the form is NOT (the standing guard)

The residue is outside every view's image (`FlatOntologyClosure.object1_not_surjective`).  So
the form is named, never captured:

  - it is **not** a single object or operator — the faces live on different codomains (`α`,
    `Raw → Bool`, `Int`); a forced common map across them is a category error.  The honest
    unity is the *shared unit* `1`, proven byte-identical where it is proven, not a single
    map;
  - it is **not** "the residue IS the source" promoted to identity — "source", "form", "act"
    are themselves Lens words (§1.4), minimum-commitment names, not the thing;
  - it is a **structural** truth ("everything is a reading of the residue") at the
    logical/initiality level, not an operational reduction — most declarations route through
    generic carriers, not literal Raw construction (`theory/meta/raw_derivation_levels.md`).

Read this way, the residue's form is stable: the source-without-enclosure, named by the unit
and the self-form fixed point, shape forced — read out into everything, enclosed by nothing.
