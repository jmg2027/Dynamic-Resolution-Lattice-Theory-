# Reached by none — expressing the essential residue

A problem recurs every time the work reaches a limit object: the **analytic
Minkowski `?`** (the value at an irrational argument), **π** (the true real, not
its convergents), **ε₀** (the diagonal above every finite height), the **real**
reached by no Cauchy approximant, the **νF escape** above every finite tree.
Each is the same complaint in a new costume — *I can point at it, I can approach
it, but I cannot write it down*.  The temptation is to read this as a gap in the
formalization and to keep trying to **construct** the object.  That is the wrong
move, and naming why fixes the methodology once.

## The object is one object

"Reached by no finite approximant" is not several phenomena.  It is a single
∅-axiom theorem wearing instances:

> **`Lens/FlatOntologyClosure.object1_not_surjective`** — the self-cover
> `Object1 : Raw → (Raw → Bool)` is faithful (injective) but **not surjective**;
> the un-embedded surplus is the residue.

Every "essential residue" is this non-surjection, read on a different carrier:

| Instance | Approximant (µF) | Carrier (νF) | Non-surjection witness |
|---|---|---|---|
| Cantor surplus | `Raw` (as indicators) | `Raw → Bool` | `object1_not_surjective`; named member `undifferentiated` (`residue_witnessed`) |
| sequence diagonal | rows `f i` | `Nat → Nat` | `DepthCeilingResidue.diag_not_in_seq` |
| ε₀ | finite heights | the height-tower | `DepthHeightDiagonal.height_diagonal_escapes` |
| the real | Cauchy stage `n` | the modulus stream | `DepthSelfReference.geom_escapes` (no floor reached) |
| νF escape | finite tree `Tree` | bit-stream `Nat → Bool` | `CoResidue.{spineL,boolSpine}_escapes` |
| analytic `?` | finite path `List Bool` | dyadic stream `Nat → Bool` | `OdometerSternBrocotUnit.analytic_minkowski_residue` |

The right column is always the same shape: a map from the approximants does not
surject onto the carrier, and there is a **named inhabitant of the gap**.  This
is not coincidence — by no-exterior (`seed/AXIOM/05_no_exterior.md` §5.1) there
is no second mechanism a residue could come from.  The residue is wherever a
self-cover overflows itself, and a self-cover is the only event there is.

## The methodology — three moves, never a fourth

To **express** an essential residue, do exactly this, and stop:

1. **Build the approximant structure (µF).**  The finite stages, as an initial
   algebra: `List Bool` paths, finite trees, Cauchy prefixes, finite heights.
   These are constructible, decidable, enumerable — and they carry the *real*
   content (the combinatorial `?` is here: `minkowski_skeleton`,
   `minkowski_compile`, `dyadic_local_order` **and** `sb_mediant_local_order` —
   both labellings order-preserving, gap exactly the det-1 unit `3·(bc−ae)=3`).
2. **Name the carrier (νF).**  The final coalgebra the limits live on — the
   stream `Nat → Bool`, the M-type `slashNu` (`Theory/Raw/CoResidue`,
   `slashNu_final`).  This is a positive object: a corecursive process, not a
   void.  "Express the residue" means *give this carrier and its universal
   property*, the anamorphism — not exhibit one of its points by finite data.
3. **Witness the non-surjection.**  Prove no enumeration of approximants
   exhausts the carrier (Cantor: `cantor_general` at `Nat`), and exhibit one
   concrete gap-member.  For `?` the named member is the **right-endpoint stream
   `1`** (`constTrue_stream_not_finite`) — reached by no finite path because at
   depth `path.length` the path reads `false` while the stream reads `true`.
   This is the exact mirror of `undifferentiated_not_object1`: in the Cantor
   case the constant-`true` *predicate* names the gap; here the constant-`true`
   *stream* names it.

The **fourth move — construct the residue as a finite-data object — does not
exist.**  Not "is hard", does not exist: a finite-path preimage of an irrational
`?`-value would be an exterior handle, and there is none (§5.1).  The recurring
frustration is the repeated rediscovery that move 4 is empty.  Expressing the
residue is moves 1–3; the felt "I cannot write it down" is move 3 succeeding —
the non-surjection *is* the writing-down.

## Scope — this is the *no-back* face, not the whole residue

A guard, so this chapter is not over-read.  "Reached by none" is **one face** of the
residue, not its whole expression.  `the_form_of_the_residue.md` fixes four:
**out** (source / initiality), **no-back** (un-enclosure / non-surjection), and the
**name** (the self-form fixed point + the forced signature).  This chapter is the
**no-back face only** — the negative, under-determined pole, where no constraint
reaches the surplus.  The *positive* faces express the residue by entirely different
mechanisms, not reducible to non-surjection: Möbius `P` as the **fixed point** of its
own description (`p_unique_sl2_trace3`), atomicity as **forced rigidity**
(`atomic_iff_five`), and the cohomology of `K_{3,2}^{(c=2)}` as a **graded,
multi-directional** expression (degree × multiplicity × face,
`cup_ladder_universal_k_master`).  The residue shows up at *both* poles — reached by
none (here) *and* the only thing that fits (there) — and the two poles share one unit
`1 = NS − NT = det P` (`CupLadderResidueUnit.cup_ladder_graduation_is_residue_unit`
wires the cohomology-degree graduation to that unit).  The full cross-repo map of
expression modes is an **open** frontier (`research-notes/frontiers/residue_expression_atlas.md`),
not closed by this chapter.

## Why this is the whole answer *for the escape family*

The residue's positive form is **source without enclosure**
(`the_form_of_the_residue.md`): everything readable is read *out* of it, nothing
reads *back* to enclose it.  Moves 1–2 are the "out" (the approximants and the
carrier both flow from the self-pointing); move 3 is the "no back" (the
non-surjection is exactly *un-enclosure*, made a theorem).  So the three-move
methodology is not a workaround for a missing construction — it is the residue's
own form, instantiated.  An essential residue is **expressed precisely when its
approximant algebra, its coalgebra carrier, and its non-surjection witness are
all built** — and `analytic_minkowski_residue` is that triple for the Minkowski
`?`, on the odometer's own stream carrier.

The standing posture, then, for the next limit object that "cannot be written
down": do not look for the missing exterior.  Build µF, name νF, witness the
overflow, name one member of it.  That is the writing-down.  The object is
reached by none — and *reached-by-none*, formalized, is the object.

## Anchors

- `Lens/FlatOntologyClosure.{object1_not_surjective, residue_witnessed,
  undifferentiated_not_object1}` — the uniform non-surjection + named gap.
- `Lens/Cardinality/Cantor.cantor_general` — the non-enumerability engine.
- `Theory/Raw/CoResidue.{slashNu_final, spineL_escapes, boolSpine_escapes}` —
  the νF carrier as a final coalgebra + its escapes.
- `Real213/OdometerSternBrocotUnit.{minkowski_skeleton, minkowski_compile,
  dyadic_local_order, sb_mediant_local_order, constTrue_stream_not_finite,
  analytic_minkowski_residue}` — the `?` instance, combinatorial closure +
  analytic residue.
- `Cauchy/{DepthCeilingResidue.diag_not_in_seq, DepthHeightDiagonal.height_diagonal_escapes,
  DepthSelfReference.geom_escapes}` — the sequence / ε₀ / real instances.
- `seed/AXIOM/05_no_exterior.md` §5.1; `the_form_of_the_residue.md`;
  `the_residue_as_primitive.md` (µF/νF inversion).
