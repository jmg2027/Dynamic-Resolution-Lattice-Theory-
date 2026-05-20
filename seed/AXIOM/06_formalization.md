# §7. Relationship to existing formalizations / documents

This §7 is an audit target list.  Each item must be cross-checked
against this axiom; discrepancies are corrected or isolated.

## §7.1 Lean formalization

The current Raw implementation in `lean/E213/Theory/` (2 elements
a, b + binary slash, anti-reflexive, commutative) is a faithful
machine representation of this axiom.  Detailed device-by-device
classification (α/β/γ/δ) + axiom × Lean cross-check:
`lean/E213/AUDIT.md`.

**Encoding note**: Lean 4 core has no primitive quotient, so Raw is
implemented as a subtype `{t : Tree // t.canonical = true}`.  The
Internal `Tree.cmp` (ordering) is an **encoding artifact** for
selecting canonical forms, not an axiom.  The axiom contains no
ordering whatsoever.  Cmp-independence is mechanically verified at
`lean/E213/Theory/Internal/RawCmpIndependence.lean`.  Full encoding-
cost catalog: `08_encoding_costs.md`.

Things that **automatically follow** from derivation (no additional
commitment to the axiom):

- `Raw.swap` (a ↔ b automorphism) — the first derivation from
  Axiom 1 "a and b have no relation other than not being equal."
- `Raw.fold` (catamorphism) — standard eliminator wrapper of an
  inductive type, the tool for constructing all Lenses.

**Lens-layer bleed** (Theory currently holds some Lens-flavored
observables): `Raw.depth` (`Theory/Raw/Slash.lean`), `Raw.leaves`
(`Theory/Raw/Levels.lean`), `Raw.fold_signed_swap` +
`Raw.fold_swap_hom` (both in `Theory/Raw/FoldSwap.lean`, merged
2026-05-18 from the former `Signed.lean` + `Hom.lean`).
Classified as *intentional convenience leak* — these are
pure-induction theorems on Tree that every Lens consumer eventually
needs, and relocating gains nothing for axiom-minimality.

**Forced shape uniqueness**: see `00_nature.md` §1.3.
`Theory/Atomicity/*` proofs (arity = 2, atomic ⇒ d = 5,
(NS, NT) = (3, 2)) are pure-ℕ propositions that *do not import*
Raw.  They sit in Theory structurally — they are part of "what
Raw must look like" — but their dependency on Raw is zero.

**Universal-Lens metatheory**: see `00_nature.md` §1.2 cross-ref.
`Meta/UniversalLens/{Core, Nat2Inj, Q213Inj, Nat3, Nat4, Q213_3,
TripleCapstone, Padding, PaddingCapstone}` formalize the "any
distinguishability framework factors through Raw" obligation.
Together with §1.3 these close axiom-uniqueness in three directions
(below/sideways/above).

## §7.2 Axiom corpus boundary

The `seed/AXIOM/` sub-directory is the sole axiom corpus.
Derivation is explored in `research-notes/` and in the Lean
metatheory layer (`Meta/UniversalLens/`).  Active narratives live
in `guide/` (deductively-ordered, T0/T1/T2/T3 tags) and
`books/{math,physics}/` (213-internal).

## §7.3 Concrete numerics — Lens or forced

Every concrete numeric in the current Lean tree (d=5, NS=3, NT=2,
1/α_em=137.036, …) is either a Lens construction or, for the
shape parameters, a forced-uniqueness theorem in
`Theory/Atomicity/`.  External `eval` substitution importing the
§3.3 prohibited list as fudge is mechanically prevented.
