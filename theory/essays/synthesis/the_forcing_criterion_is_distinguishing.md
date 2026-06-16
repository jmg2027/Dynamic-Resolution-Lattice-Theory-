# The forcing criterion is a distinguishing

A quantity is **forced** in 213 exactly when it is the count-Lens reading of
a genuine distinguishing — an axis on which `Raw` actually distinguishes.  A
"parameter" that adds no new distinguishing is a Lens choice (a
re-presentation), removable, never forced.  There is no third status.

## 213-native answer

`seed/AXIOM/07_primacy.md` §7.2 states the dichotomy with no remainder:
everything other than the axiom is either **derived from the axiom** or the
**result of an explicit Lens choice**.  A genuinely "free parameter" has no
operand — 213 commits to no exterior dialer such a parameter could be set from
(`seed/AXIOM/05_no_exterior.md` §5.1).  So the question "is `q` forced?" is
not metaphysical; it is the decidable question **does `q` name a distinguishing
axis, or a reading laid on one already present?**

## Derivation

The forced atoms are the genuine distinguishings.  `(NS, NT) = (3, 2)` is
forced because it is the unique non-decomposable atom pair
(`Theory/Atomicity/PairForcing`, `Five`); `d = NS + NT` is definitional;
**arity 2** is forced because the distinguishing slash is binary — a real
property of the relation's inputs (`Theory/Atomicity/CombinatorialArity`, the
uniform pigeonhole `pigeonhole_fin_to_fin2`).  Each is an axis on which Raw
distinguishes; none can be dialed.

The criterion's sharp edge is what it *excludes*.  The edge multiplicity `c`
of `K_{NS,NT}^{(c)}` is **not** an arity and not a distinguishing axis: the
gauge content `NS² − 1 = 8` is already a fact about the forced `NS = 3`
(`Couplings/SpectrumComplete.alpha_3_channel`), and the graph cohomology
`b₁ = 6c − 4` merely *crosses* that constant at one point —
`Cohomology/Cup/K32Projection.k32_b1_32_crosses_adjoint_only_at_2` proves
`c = 2` is a selected crossing of a c-line with a c-constant target, not a
forcing.  `c` adds no distinguishing; it re-presents `NS²−1`.  Hence it is
removable, and removing it changes no observable
(`theory/physics/foundations/atomic_constants.md`).

The same criterion runs in pure number theory, with the opposite verdict.
A function is multiplicative exactly when it is a readout of the ×-count-Lens
— the prime-exponent vector `vp` — and that readout is **faithful because the
×-atoms (primes) are distinguishable**: `Meta/Nat/VpSeparation.vp_separation`
(which *is* the fundamental theorem of arithmetic) is the statement that the
distinguishing axes separate (`theory/essays/synthesis/multiplicativity_is_the_x_count_lens.md`).
Coprimality is disjoint support across those axes.  Here the axes *do*
distinguish, so the readout is forced and faithful — the mirror image of `c`,
where no axis distinguishes and the readout is free.

So one test adjudicates both: **forced ⟺ a genuine distinguishing axis;
faithful ⟺ the axes separate; removable ⟺ no axis is added.**  `vp_separation`
is the criterion returning *yes* (primes separate → multiplicativity forced);
the c-removability audit is the same criterion returning *no* (no axis added →
`c` not forced).

## Dual function

Classically these wear two unrelated names — a "fundamental constant" versus a
"free parameter."  213 strips the packaging to one distinction: a fundamental
constant is a forced distinguishing (nothing to dial), and a free parameter
has no operand at all (no exterior, §5.1), so the supposed freedom is empty.
The refinement is that "forced" becomes *syntactic* — it is "names a
distinguishing axis, faithful by a separation theorem" — and therefore
testable: `vp_separation` is proven, `c`'s non-forcing is proven.  The word
"forced" stops being rhetoric and becomes a `#print axioms`-checkable property.

## Cross-frame connections

The criterion is one fact seen in five frames: §7.2's *derive-or-Lens-choice,
no third option*; the forced/read split at the physics scale
(`theory/essays/synthesis/what_213_forces_and_what_it_reads.md` — forced
numbers, read names); `vp_separation` as faithfulness of the ×-atoms; the
c-removability audit as a missing distinguishing axis; and the residue/Lens
non-surjection (`Lens/FlatOntologyClosure.object1_not_surjective`) — a Lens
output is never the residue, so a Lens-output number (like `b₁(K^{(c)})`) is
never itself a forced atom.  The honesty audits of the deleted programmes were
this criterion applied as hygiene: a `:= True` "conjecture", a `chartVisibleAxes
:= NS+NT−1` "dimension", a typed `:= 137` "prediction" are all readings dressed
as distinguishings — re-presentations mislabeled as forced.

## Open frontier

The criterion is stated and instantiated at both poles but not abstracted: a
single 213-native lemma of the form *"a readout is faithful/forced iff its
indexing axis distinguishes"* that both `vp_separation` and the c-removability
result are instances of, is not yet written
(`research-notes/frontiers/crossdomain_divisor_x_branch_merge.md` §3).  Until
it is, "forced ⟺ distinguishing" is a verified pattern across cases, not a
proven meta-theorem.
