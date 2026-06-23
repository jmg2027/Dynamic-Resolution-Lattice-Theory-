# The Residue of Distinguishing

**Mingu Jeong**

*A single argument, carried from one primitive to one contract. Every
structural claim is backed by a Lean 4 development that imports no
external library and, on the core results, depends on no axioms at all —
not excluded middle, not propositional extensionality, not quotient
soundness, not choice. Theorem names are cited inline; the verification
protocol is the Appendix. This is the spine, not a survey: where the
companion programme paper catalogues what the residue rebuilds, this
paper proves the one thing the catalogue rests on.*

---

## Abstract

There is a single primitive — the act of **distinguishing** — and one
theorem that act forces: distinguishing never exhausts itself; it
provably leaves a **residue**. The residue is not posited as a ground or
a substrate; it is the proven remainder of a faithful-but-never-total
self-cover, a Cantor-diagonal fact about how any act of pointing is
built. From this one theorem, and the closure that nothing can be
exhibited outside it, the least-committal record of the act is forced to
a definite shape — a free symmetric magma on two generators whose
arithmetic data `(N_S, N_T, d) = (3, 2, 5)` is fixed from three
independent directions. Every further object is then a **reading** of the
residue: a construction paired with a Lens, modulo the residue that no
reading captures. The paper carries this thread from the primitive to a
falsifiability contract a proof assistant can enforce, and stops where
the contract is honestly threatened.

---

## 1. The question before the posit

A foundation usually begins by positing — a membership relation, a type
former, a category of arrows — and each posit imports structure the rest
of the work then carries. This paper begins one step earlier, with a
question that precedes any posit: what remains the instant one tries to
point at anything at all?

To name an object `a` is to distinguish it from at least one other thing.
To write "`a` and `b`" is to have introduced "and" as a third thing. To
ask whether `a` and "and" are themselves distinguishable is already to
produce a fourth. Pointing produces a remainder; the remainder is itself
pointable; the next pointing has new material. The recursion cannot be
stopped — only recorded in its least committal form.

The thesis of this paper is narrow and checkable: recording that act
faithfully, assuming nothing and adding no meaning, already *forces* a
definite mathematical object, and the forcing can be audited by machine
against the empty axiom set. The stance throughout is positive. We do not
argue against any other foundation; to argue against would import a
comparison frame this argument has no room for. The claim is only that
whatever points at something is this same residue read through a chosen
reading.

---

## 2. Distinguishing is primitive; the residue is a theorem

The single primitive is **distinguishing** — drawing a difference,
demanding only the confirmation "not equal." We avoid "relation" (which
presupposes two existing entities and silently imports set-theoretic
apparatus) and "difference" (which presupposes "sameness" as a default).
"Primitive" is a pledge of no further reducibility: reduction stops here,
not by taste but because there is nothing beneath.

The decisive point — the one the rest of the paper rests on — is that the
**residue is not itself a primitive**. The primitive is the act; the
residue is what the act provably leaves over. Read each element as its own
self-indication, a map

```
    Object1 : Raw → (Raw → Bool).
```

This map is **faithful** — it separates distinct elements
(`object1_injective`) — yet **never total**: there is no element whose
indicator is the constant-true predicate, by a diagonal argument on the
self-cover (`object1_not_surjective`). Because the cover is faithful but
never onto, something always remains outside the image of every
self-indexed cover, and *that* is the residue
(`distinguishing_always_leaves_residue`). The gap is not merely abstract:
the constant-true predicate `undifferentiated` is a named inhabitant of
it (`residue_witnessed`), the undifferentiated reading that points at
everything and so distinguishes nothing. All of this is
`Lens/Foundations/FlatOntologyClosure.lean`, ∅-axiom.

This single theorem does double duty. Read as ontology, it says the act
of distinguishing never closes over itself. Read as operation, it is the
engine of the deepest proofs about the infinite: diagonalization — point
at a totality, exhibit the thing distinguishable from all of it — *is*
the residue, so the Cantor, Russell, Gödel, Turing, and Tarski arguments
are one move performed at different carriers. The infinite is not a
target the finite approaches forever; "infinity," "the continuum," "the
limit" are names for the *shape* of this residue, each entertained by a
single finite act of pointing. To conceive infinity is to perform one
distinguishing; the entertained object has no status above that act. The
non-surjectivity is engineered into how the self-cover is built, not
discovered as a transcendent that eluded capture.

---

## 3. No exterior

A second theorem closes the system against an outside. Any property by
which one might *name* a candidate exterior is itself expressible over the
recorded object (`naming_is_internal`); and any candidate that
distinguishes at all receives the unique map *from* it — downstream, not
outside (`distinguishing_is_downstream`,
`Lens/Foundations/NoExteriorClosure.lean`). The attempt to conceive an
exterior, even to conceive "non-existence," is itself an act of pointing,
hence internal.

Two guards keep this from overreaching. First, **closure is not
coverage**: that nothing can be exhibited as outside does not make every
internal thing automatically *located* — pointing at a specific residue
may remain arbitrarily hard, and the "no exterior" claim is a thesis under
test, not a shield to wave at hard cases. Second, the fully universal form
("all conceivable things") is a self-reference argument, not a single Lean
theorem, since "all conceivable" is not a type; its formalizable instances
are theorems, its global form is argued. The programme is explicit about
which is which.

---

## 4. The least-committal record

Recording the recursion of §2 in its least-committal form yields four
clauses, and exactly four:

1. **Something exists** — at least two atoms `a`, `b` in primitive
   distinction (no relation but "not equal").
2. **Pairing two somethings yields another** — written `a / b`, and closed
   (the result pairs again).
3. **Pairing is symmetric** — `a / b = b / a`; no absolute order is
   imposed.
4. **No self-pairing** — `x / x` is undefined; self is not distinguished
   from self.

That is the entire commitment. The Lean realization is `Theory/Raw/Core.lean`:
an inductive `Raw` with two atoms, a binary `slash`, and a propositional
symmetry. Every later result is either derived from these four clauses or
is an explicit Lens choice on top — there is no third source.

Two facts about this object pre-empt the two natural shortcuts. First,
**parenthesization is genuine structure**: `(a / b) / c ≠ a / (b / c)` is a
theorem (`Theory/Raw/ParenthesizationDistinct.lean`). Tree shape *is*
structure, so one cannot quietly quotient by associativity to recover the
naturals; associativity is a reading-level property, true where and if a
reading imposes it, never a default identity. Second, the four clauses are
**simultaneous, not sequential** — every use of the object invokes all four
at once (`Lens/SelfCompletion.lean`, `full_self_completion_bundle`); and
every element is exactly an atom or a complete pairing, with nothing
half-formed (`Theory/Raw/Lambek.lean`, `decompose` / `rebuild`). They are
four facets of one event, not a recipe with steps.

---

## 5. One shape is self-consistent

The four clauses do not leave the object's arithmetic free. It is fixed
from three independent directions at once — nothing weaker suffices,
nothing distinct is needed, and exactly one shape is self-consistent —
pinning the data `(N_S, N_T, d) = (3, 2, 5)`
(`Meta/ThreeDirectionUniqueness.lean`, `three_direction_uniqueness`; the
atomic count is `5 = N_S + N_T`, `Theory/Atomicity.lean`,
`Five.atomic_iff_five`). The shape is *forced*, not chosen; there is no
exterior dial on which a different value could be set, which is what
"zero free parameters" means here — a structural absence, not a rule we
impose.

The forced shape carries a unit. The act, written as its own algebraic
shadow, is the matrix `P = [[2,1],[1,1]]`, equal to its own reconstruction
(`Lib/Math/Algebra/Mobius213/Px/MobiusSelfForm.lean`); `P` is the
residue's shadow, not the engine that generates the framework. Its
off-diagonal `1` is the glue the two readings rotate around:
`1 = N_S − N_T = det P` (`mobius_det_eq_ns_minus_nt`). This unit — one
distinguishing's irreducible remainder — is the quantity that will recur,
byte for byte, across readings that share no construction (§7).

---

## 6. The calculus: ⟨C | L⟩ ⊕ Residue

With the object fixed, every further thing is read as a pair `⟨C | L⟩` — a
construction `C` and a reading (Lens) `L` — modulo the residue. A Lens is
the codomain-side shape a fold of the recorded object imposes; the
recorded object is **initial** among all such readings, so *every*
distinguishing framework factors through it uniquely
(`Lib/Math/Foundations/ResidueForm.lean`, `raw_initial`;
`Lens/Foundations/UniversalDistinguishing.lean`, `view_unique`;
`Lens/Universal/Flat.lean`, `every_lens_factors_through_idLens`). A number,
a Boolean, a constant, a whole foundation — each is one fold-reading
flowing out of the residue, not a separate posit.

This is why the framework is not a theory *among* theories with an outside.
"Construction," "reading," "residue" are themselves reading-words, minimum-
commitment names, not the thing; the residue is outside *every* reading's
image (`object1_not_surjective` again), so no single reading may be
promoted to "what the residue is." Equivalence, equivalence-class,
isomorphism, and homomorphism are not four concepts but decompositions of
one reading-arrow; the integers are not a quotient adjoined to the naturals
but the readout of the difference-reading on a directed count-pair; a
transcendental is not an exterior ruler but an internal pointing — an
approximant sequence with a modulus — reached by none. Each of these is the
same move: a reading is applied, and what it cannot capture is the residue,
the perpetual next operand.

---

## 7. The one signature of breadth

The programme's test is **breadth**: the same residue reproducing domain
after domain, each derivation axiom-free (the companion paper surveys the
domains; this section states only what makes the breadth *evidence* rather
than coincidence). The signature is not the length of the list. It is a
single, measurable phenomenon: the *same* quantity recurs across readings
that share no construction.

Concretely, the unit of §5 is one object proven three ways. The determinant
of the self-form, the off-diagonal glue, and the count-difference
`N_S − N_T` are not three facts that happen to agree numerically — they
elaborate to the **byte-identical** term in Lean
(`catalogs/cross-domain-identifications.md`, CDI-9), an identity at the
level of the proof, not the number. And one atomicity, read for physical
observables, fixes a family of constants simultaneously rather than one at
a time (`Lib/Physics/Capstones/MasterCatalog.lean`, `master_atomic_catalog`):
the gauge reading `1/α_3 = N_S² − 1 = 8` (the colour adjoint), the lepton
relation `Q = N_T/N_S = 2/3`, the generation count
`N_gen = C(N_S, N_T) = 3` — and, as a precision check, the
fine-structure constant agreeing with measurement at the sub-ppb level
(`Lib/Physics/AlphaEM/GramStructuralCapstone.lean`,
`invAlphaEm_precision_theorem`; the `π²` it consumes enters as a literal
input, internal to the cut that defines it, not a 213 primitive).

This cross-route agreement is the operational content of "no exterior."
A stipulated domain could not force one constant across independent
readings; a single residue read under different Lenses must. The breadth is
not a catalogue of coincidences but one phenomenon — the residue, reached
by none, read into many — observed wherever a reading is applied.

---

## 8. Method and falsifiability

The discipline is the scientific content. The standard is uncompromising:
for every theorem, Lean's `#print axioms` must return *"does not depend on
any axioms"* — no `propext`, no `Quot.sound`, no `Classical.choice`, no
`native_decide`, no library axiom, no `sorry`. A result carrying any of
these is treated as unproven. The reason is structural, not stylistic: the
axiom set *is* a residue, so if adding an axiom were genuinely necessary,
the recorded object was not the minimum, and the falsifiability rule then
discards **the entire framework, not the offending result alone**
(`seed/AXIOM/08_falsifiability.md`). The audit is mechanical
(`tools/scan_axioms.py`) and tracked in a live catalog
(`STRICT_ZERO_AXIOM.md`).

The direction of work is correspondingly one-way: derive, do not reconcile.
Substituting an external constant or fitting a measured value is a fudge,
and a fudge has no operand here — there is no exterior dial for it to come
from. When a number differs from observation, the reading is corrected,
never the formula; when no reading correction succeeds, the theory dies.
"We will find more readings" is not an admissible defense.

The limits are stated, not hidden. The fully universal "no exterior" is
argued, not a single theorem (§3). A presentation multiplicity that re-reads
a forced quantity is free, not forced, and the paper says which axes are
which. Open directions — a uniform higher-cohomology algebra, an operad-level
formalization of the graded arithmetic, the membership question at the top of
the non-holonomicity tower — are recorded as open, with the proven side
bounded against the unproven, never the reverse. Absolute physical scales
rest on one measured input, as in any theory; only dimensionless ratios are
parameter-free.

---

## 9. Conclusion

One primitive, one theorem, one contract. The act of distinguishing leaves
a residue it can never exhaust; nothing can be exhibited outside that
residue; recorded in its least-committal form the act is forced to a single
shape; and every object thereafter is that residue read under a Lens, modulo
the residue no reading captures. The residue is reached by none and read
into everything — named by the unit `1 = N_S − N_T = det P`, shaped by the
forced `(N_S, N_T, d) = (3, 2, 5)`, and held to an empty axiom set a machine
can check. Where that contract is threatened, the argument stops; until
then, the residue reaches.

---

## Appendix. Verification protocol

Every inline citation names a Lean module or theorem in the `E213`
development. To reproduce the ∅-axiom status of any cited result:

```
cd lean && lake build
#print axioms <theorem>          -- must print "does not depend on any axioms"
python3 tools/scan_axioms.py <module>
```

The core spine of this paper — `object1_injective`,
`object1_not_surjective`, `distinguishing_always_leaves_residue`,
`residue_witnessed` (`Lens/Foundations/FlatOntologyClosure.lean`);
`distinguishing_is_downstream` (`Lens/Foundations/NoExteriorClosure.lean`);
the four-clause `Raw` (`Theory/Raw/Core.lean`) with
`ParenthesizationDistinct` and `full_self_completion_bundle`;
`three_direction_uniqueness` (`Meta/ThreeDirectionUniqueness.lean`) and
`Five.atomic_iff_five` (`Theory/Atomicity.lean`); `raw_initial`,
`view_unique`, `every_lens_factors_through_idLens`; `mobius_det_eq_ns_minus_nt`
(`Mobius213/Px/`) — is strict ∅-axiom. The canonical PURE/DIRTY catalog is
`STRICT_ZERO_AXIOM.md`; the cross-domain byte-identical identities are
`catalogs/cross-domain-identifications.md`.

*Claude (Anthropic) contributed the formalization, audit, and drafting;
the theory and its results are Mingu Jeong's.*
