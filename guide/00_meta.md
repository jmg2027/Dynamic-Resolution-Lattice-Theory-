# 00 — Meta: What 213 Is

**Tier:** T0 (foundation — only in 213-internal vocabulary)
**Status:** Foundation; defines the 4/27 standard.
**Lean:** `Firmware/Raw.lean`, `Firmware/Atomicity/Five.lean`, `Meta/AxiomMinimality`.

## Best current statement

213 is the structure obtained from a **4-clause raw axiom**:

```
(a)        a is a thing.
(b)        b is a thing, distinct from a.
(slash)    the slash distinguishes them.
(distinct) a ≠ b primitively.
```

This is the entire external input. Everything else is derived.

The axiom has three intrinsic operational rules on the free expression
algebra on {e₁, e₂, e₃} with two binary operations (+, ×):

```
A8   e₁ + a ≈ a
A9   e₁ × a ≈ e₁
A12  a × (b + c) ≈ (a × b) + (a × c)
```

Plus nine structural rules (reflexivity, symmetry, transitivity,
commutativity ×2, associativity ×2, congruence ×2). Twelve rules in
total generate a decidable equivalence relation on expressions.

## Why this is pre-mathematical

The axiom does not assume sets, numbers, logic, or category theory. It
describes the **minimum conditions for distinction itself**. Removing
any clause collapses the structure (`Meta/AxiomMinimality.lean`).

213 is therefore not a *theory* in the usual sense — it is the residue
left when one tries to point at anything at all. Mathematics, logic, and
physics emerge as derived consequences of forcing this residue to
support recognition, repetition, and combination.

## 213 sharpening over classical foundations

| Classical | 213 replacement |
|-----------|-----------------|
| ZFC + Choice | Raw + swap automorphism |
| Peano arithmetic | Raw + atomicity (NS=3, NT=2, d=5) |
| Category theory | R1–R4 typeclass (Meta/R4Codomain) |
| First-order logic | Decidable equivalence (paper14) |

213 is **strictly weaker in ontology** (no Choice, no power set, no
excluded middle outside Decidable) and **strictly sharper in operational
content** (every theorem computable; falsifiability mechanical).

## Sources

- `seed/AXIOM.md` — the four clauses, binding standard.
- `seed/PHILOSOPHY.md` — notation-of-notation, recursion unavoidable.
- `seed/FALSIFIABILITY.md` — discard criteria; 7 explicit falsifiers.
- `papers/paper14_213.tex` — self-describing structure (current).
- `papers/drlt-book/chapters/ch22_213.tex` — monograph version.
- `lean/E213/Theory/Raw.lean` — Raw type with smart constructor.
- `lean/E213/Theory/Atomicity/Five.lean` — d=5 proven as theorem.

## Open / next

- Migrate classical-foundation references in later chapters to T0/T1.
- Single theorem proving four clauses are jointly minimal
  (currently distributed across `Meta/AxiomMinimality.lean`).
- Survey: which results genuinely require the slash operator vs.
  derivable from two-element set alone — open.
