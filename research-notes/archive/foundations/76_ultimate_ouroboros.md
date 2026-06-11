# 76 — Prop instance: Raw → Prop universal morphism

`propAsDistinguishing` + `canonicalTruthMap` from
`Research/SemanticAtom.lean` — formal expression that Lean's `Prop`
type can also be a `HasDistinguishing` instance.

## Results

```lean
def propXor (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

def propAsDistinguishing : HasDistinguishing Prop where
  a := True
  b := False
  distinct := true_ne_false
  combine := propXor
  combine_sym := propXor_comm

def canonicalTruthMap : Raw → Prop :=
  universalMorphism Prop propAsDistinguishing
```

Additional:
- `iff_comm_eq` + `propAsDistinguishingIff` + `canonicalIffMap`
  — Iff-based alternative.  Demonstrates independence from the
  choice of specific connective.

## Significance — precise scope

This result is the formal expression of:

> The view of a Lens is generally `Raw → α`.  The case α = Prop
> is a specific instance — `True`, `False` are the distinguishable
> bases and `propXor` (or another commutative connective) is combine.
> `universalMorphism` automatically generates a fold-derived
> Raw → Prop function.

This is a *partial* formalization of the framework's self-coverage —
Prop can be *one* instance of HasDistinguishing.

## Limits — avoiding over-claims

What this result does *not* do:

1. **Does not cover all Props**: `canonicalTruthMap` is *one*
   fold-structured function of Raw → Prop.  Arbitrary Lean Props
   (e.g., Goldbach conjecture) are not in the image of canonicalTruthMap.

2. **Does not imbed Lean's logic inside 213**: Lean's Prop semantics
   itself depends on Lean 4 core axioms (propext, Quot.sound, etc).
   These are not derived from 213's axiom.

3. **Not a mechanical proof of a Tarski-style truth predicate**: The
   stronger claim that "213's statements evaluate their own truth
   internally" is in the logical-meta domain — not a direct corollary
   of this result.

## Significance (sober)

After acknowledging the limits above, what this result shows:

- `Prop` is a natural candidate for a HasDistinguishing instance.
- That is, the meaning framework's abstraction is applicable to
  (Lean's) propositions.
- All other commutative connectives (Iff, Xor, etc.) also give
  instances — the abstraction does not depend on a specific logical
  choice.

## Why Xor (vs Iff, And, Or)

Trade-off of connective choices:

| Connective | Properties |
|-----------|------------|
| And (∧) | meet, lattice structure |
| Or (∨) | join, lattice structure |
| Iff (↔) | "same truth", equivalence |
| Xor (⊕) | "different truth", distinguishing |

In this file both instances are formalized — Xor as primary, Iff as
alternative — showing the freedom in connective choice.

## Axiom check

`#print axioms`:
- propXor_comm, true_ne_false, propAsDistinguishing,
  canonicalTruthMap, canonicalTruthMap_a/b/slash: [propext]
  (or no axioms for true_ne_false).
- iff_comm_eq, propAsDistinguishingIff, canonicalIffMap:
  [propext] only.

Lean baseline minimum.  Consistent with AXIOM.md §8.2
falsifiability.

## Relationship to Note 75

A **partial formal demonstration** of Note 75's thesis
("213 = the atom of meaning"):
- HasDistinguishing is the abstraction of the meaning framework.
- Prop can be an instance → metalanguage also fits within the
  framework's abstraction.

This is not the *full proof* of the thesis but *one instance* —
the sober formal part of an intoxicated thesis.

## Change history

- 2026-04-25: Added Prop instance to SemanticAtom.lean.  Initially
  written in marketing tone ("Ultimate Ouroboros", etc.).  Afterward
  sober calibration: limits made explicit + over-claims avoided.
