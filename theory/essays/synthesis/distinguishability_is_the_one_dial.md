# Distinguishability is the one dial

Three structural facts that look like three separate theorems — why relations
are forced to arity 2, why `+` and `×` commute but `^` does not, and why `×`
carries more information than `+` — are one fact read at three resolutions. The
single parameter is whether the atoms being related are **distinguishable**.

## 213-native answer

A Lens reads a `Raw` by deciding, atom by atom, whether two things are the same
or different. Everything an operation can carry is exactly what that decision
keeps: where atoms are *indistinguishable*, structure collapses to a bare count;
where they are *distinguishable*, the arrangement survives as information. "The
one dial" is that decision itself — `slash`'s `x ≠ y` (forced by the axiom + the
no-`Quot.sound` rule, `seed/AXIOM/01_residue.md`). Turning it gives all three
phenomena below; they are not analogous, they are the same turn.

## Derivation

**Resolution 1 — arity is forced to 2.** A relation step that distinguishes
nothing relates no two distinct positions, so it does no work. The arity-forcing
result makes this exact: the relation arity is forced to 2 because the step
relates *distinct* positions through the clause-4 distinctness gate
`i ≠ j → f i ≠ f j` (`Theory/Atomicity/ArityForcingComplete.arity_two_forced`,
with `exists_distinct_iff_two_le` the hinge — below arity 2 there are no two
distinct positions to gate on). Arity 2 is the *minimum at which the dial is on
at all*: one distinguishing needs two distinguishable slots.

**Resolution 2 — commutativity lives and dies by the dial.** On lists of
indistinguishable units, append commutes — arrangement is no information, so
`[ ]++[ ] = [ ]++[ ]` collapses (`Meta/Nat/UnitList.append_comm`). On
*distinguishable* elements it does not: `[a]++[b] ≠ [b]++[a]`
(`append_not_comm_general`). This is the whole content of where commutativity is
born (`theory/essays/analysis/where_commutativity_is_born.md`): `+` commutes
because a unit list's count is order-free; the count-shadow `add_comm_from_append`
is the dial reading *off*. At the `^` rung the dial turns *on* in a new place —
`^` has two arguments of different kinds, a side and a dimension, and swapping
them changes the object (`Meta/Nat/UnitHyper.swap_changes_dim`,
`dim (hcube 2 3) ≠ dim (hcube 3 2)`), so non-commutativity is that asymmetry read
by the count (`theory/math/numbersystems/arithmetic_generation.md`, the operation
tower).

**Resolution 3 — the +/× gap *is* the dial.** The exact excess of `×` over `+`
is the distinguishability of atoms, and nothing else. One construction — two
blocks `replicate j _ ++ replicate k _` — read two ways: additively (`count`) the
blocks **merge** into `j + k` because the units are indistinguishable;
multiplicatively (`prodL`) with *distinct* atoms `p ≠ q` they stay **separate** as
the exponent vector `p^j · q^k`, the pair `(j,k)` recoverable
(`Meta/Nat/ProdCount.prodL_two_atoms`). Make the atoms indistinguishable (`q = p`)
and `×` collapses back to `+`: `p^(j+k)`
(`ProdCount.prodL_one_atom_merges`) — exactly the additive `j + k`, one fold up.
So unique factorization, the exponent vector, the entire surplus of
multiplication, is the dial held *on* over distinguishable primes
(`theory/essays/synthesis/multiplicativity_is_the_x_count_lens.md`).

## Dual function

Read classically, this is three familiar facts — relations are binary, addition
and multiplication are commutative monoids, the integers factor uniquely — with
their shared cause made visible: each is a statement about *information-carrying
under an equivalence*, which is what "distinguishable" names once the redundant
packaging is stripped. 213's refinement is that the cause is one syntactic
switch, not three coincidences: the same `slash` decision that forces arity 2
also kills `+`-commutativity's converse and opens the exponent vector. Where the
classical account has three theorems proved by three methods, here one dial moves
and all three follow as count-shadows.

## Cross-frame connections

The dial appears in at least four frames as the same act:

- **Generation boundary** — ℕ's additive/equational/order structure is generated
  on the distinguishing's own structural descent, but FTA needs a non-structural
  descent over *distinguishable* prime atoms
  (`theory/math/numbersystems/arithmetic_generation.md`, "where generation
  stops"). The boundary of generation is exactly where the dial flips from off
  (indistinguishable units, structural peel) to on (distinguishable primes).
- **Forcing criterion** — a quantity is forced ⟺ it names a genuine
  distinguishing axis (`the_forcing_criterion_is_distinguishing`); the dial *on*
  is "a separating axis exists," the dial *off* is "no axis added."
- **Faithfulness** — `forced_by_the_distinguishing` already states the additive
  and ×-count Lenses are one act on two axes, ×-atoms distinguishable where
  +-atoms are not; that essay's `vp_separation` faithfulness is the dial *on* in
  multiplicative number theory.
- **The failure-mode catalog** — "Count-Lens import as Raw" (`2` is a count, not
  a Raw cardinality) is the dial *off* misread as ontology.

Same switch, four resolutions — arity, commutativity, factorization, faithfulness.

## Open frontier

The dial names *where* generation stops but does not yet *generate* the on-state.
A Raw-native multiplicative descent — a prime-distinguishability structure that
produces FTA on its own well-foundedness rather than the borrowed
`Nat.strongRecOn` — was the open frontier, now closed (the grounded FTA chain,
`theory/math/numbertheory/grounded_fundamental_theorem.md`). Even so "distinguishable
prime atoms" is a recognized terminus, not a generated one: the dial's on-state is
described, the engine that turns it on at the multiplicative rung is not yet
built.
