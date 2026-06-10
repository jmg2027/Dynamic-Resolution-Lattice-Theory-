# Finite-state-ness is a property of the pointing, not the value

Whether a `±1` is "finite-state" is undecidable as a question about the `±1` — it is a question
about the *process that produces it*.  The same value carries a bounded process and an unbounded
one at once, so the predicate "finite-state" attaches to the pointing, never to the pointed-at.

## 213-native answer

"Finite-state" / "holonomic" is the predicate **"in the image of a finite-stage (bounded-memory)
cover"** — and a cover is a *pointing*, not a value.  The decisive witness is a single inhabitant
with two verdicts: `(-1)² = 1` (`Padic/NuEscape.neg_one_sq_eq_one`).  The **result** is the trivial
element `1`; the **carry** computing it, `mulCarry (-1)(-1) k`, is unbounded
(`mulCarry_unbounded`) and is itself a νF inhabitant reached by no finite Raw (`carry_is_nu_escape`).
Addition's carry, by contrast, is one bit (`add_carry_le_one`).  One value `1`, a finite-state
pointing (`+`) and a non-finite-state pointing (`×`) — so "finite-state" cannot be a fact about `1`.

## Derivation

The same structure appears, proven independently, one domain over — on sequences.  A sequence whose
**Casoratian determinant** is the unit `q = −1` has **no finite holonomic depth**:
`Analysis/Cauchy/WronskianDepth.cas_neg_unit_no_finite_depth`, the maximum-entropy ceiling of
`Algebra/DetSpectrumPoles`.  The determinant — the *value* — is the unit `±1`; the *generation* — the
recurrence depth — escapes every finite-state machine (`MaxEntropy (cas s)`).  This is the
ring-operation fact (`mul_carry_nu_residue`: `(-1)²=1` with an escaping carry) read at the
sequence scale: a unit determinant whose generating recurrence is non-finite-state.

Both are one reading of `Lens.Cardinality.cantor_general` / `FlatOntologyClosure.object1_not_surjective`
run *on the process*.  The finite-stage machines are a cover; the non-finite-state process is the
escapee; "holonomic = in the image of the finite-state cover" is the schema
`CoResidue.escape_by_invariant`, with the carry / the depth its escapee
(`carry_is_nu_escape` = `escape_by_invariant` at the `Nat`-carry alphabet).  Because the escapee is
fixed by the cover, the *same* value sits inside one cover's image (the `+1`-carry, the unit
Casoratian `cas_unit_depth0`) and outside another's (the `×`-carry, the `q=−1` Casoratian) — which
is exactly "the verdict is not a property of the value."

## Dual function

The classical packaging — "multiplication is harder than addition", "this sequence is not C-finite"
— names a difficulty and attributes it, vaguely, to the object.  Stripped: *describability by a
finite-state machine is a property of the generating process, and one value admits processes of both
kinds.*  213's refinement is the typing: "finite-state" is a predicate on the cover (the carry, the
recurrence), witnessed false-for-the-value by `(-1)²=1` — the result is `1` while the process
escapes, so no amount of looking at `1` decides it.  The classical "harder" becomes the precise
"its pointing is outside every finite-state cover."

## Cross-frame connections

The same non-surjection is three resolutions:
- **ring-operation scale** — the `×`-carry escapes finite state (`mulCarry_unbounded`), the `+`-carry
  is the bounded unit (`add_carry_le_one`); the odometer's carry is the residue unit.
- **sequence scale** — the `q=−1` Casoratian has no finite holonomic depth
  (`cas_neg_unit_no_finite_depth`), against `cas_unit_depth0` (the `q=+1`, depth-0 case);
  `non_holonomicity_as_finite_state_escape` is the same fact for term-window memory.
- **description scale** — no finite catalog of framings is closed under its own diagonal
  (`object1_not_surjective`); the reframing recurs because a *closed* self-description is unavailable
  (`why_the_reframing_recurs`, falsifiability-disciplined).

All three: a finite-stage cover, non-surjective onto its own behaviour, the escapee its diagonal —
read on a number's arithmetic, on a sequence's recurrence, on a reasoner's framings.  The
presentation-dependence is the same one already proven for the reals: a cut-decision is invisible
under rescaling and depends on the approximant sequence, not the real
(`Real213/PresentationDependence`, `rcut_rescale`).

## Open frontier

A single ∅-axiom term with **both** the p-adic carry and the Casoratian depth as instances of "unit
value, non-finite-state pointing" — the cross-scale unifier — is open: `σ_a` lives in finite mod-`p`
permutations (Zolotarev), `mulCarry` on infinite `ℤ_p`, `cas` on integer sequences; the shared
invariant is named (`one_carrier_crossdomain`) but not one theorem.  And ℝ's cut is *not* a clean
not-finite-state theorem (`cutBits r N` reads only `r.xs N`, eventually constant per real) — its
"transport-only" status is honest prose, not a `mulCarry_unbounded`-style result; a real ℝ
not-finite-state result needs a transducer / unbounded-modulus framework.

## Constructive accessibility

Point at the two carries of one value.  `add_carry_le_one : Zp.carry p x y k ≤ 1` — a bit.
`mulCarry_unbounded : ∀ C, ∃ k, C < Zp.mulCarry p (neg_one) (neg_one) k` — no bound.  And
`neg_one_sq_eq_one : ∀ k, (Zp.mul (neg_one) (neg_one)).digits k = (ZpSeq.one …).digits k` — the
product is `1`.  Same `1`, carry `≤ 1` vs carry `→ ∞`: the predicate is on the carry, not the `1`.
