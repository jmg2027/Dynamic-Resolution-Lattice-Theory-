# 10 — Session 4: Cayley + Sedenion layers

Follow-up to sessions 1–3.  The CD tower now has **three
layers** formalised in Lean (layers 0, 1, 2 in full, layer 3
structurally).

## What landed

### Cayley (`framework/E213/Research/Cayley.lean`)
```
Cayley := Lipschitz × Lipschitz
```
Structure + `mul` + `conj` + three generators `I', J', L`.

Formally proved:
- `conj_conj` — involutivity.
- `conj_ne_id`.
- `mul_not_commutative` — `∃ u v, u*v ≠ v*u` (inherited).
- `mul_not_associative` — `∃ u v w, (u*v)*w ≠ u*(v*w)`.
  **The octonion non-associator.**  Closed by `decide` on
  `I', J', L`.
- `I'_ne_zero`, `J'_ne_zero`, `L_ne_zero`.
- `mul_generators_ne_zero` — three pairwise products non-zero.

### Sedenion (`framework/E213/Research/Sedenion.lean`)
```
Sedenion := Cayley × Cayley
```
Structure + `mul`.  Cayley `Add/Neg/Sub` supplement added.
R3-failure zero-divisor witness deferred (requires CD basis
mapping).

## CD tower status

| Layer | Name      | R2 | R3 | assoc | Lean state |
|-------|-----------|----|----|-------|----|
| 0 | ZI (Gaussian)  | ✓  | ✓  | ✓     | full R4Codomain instance |
| 1 | Lipschitz      | ✗  | ✓  | ✓     | non-comm + conj + anti-dist |
| 2 | Cayley         | ✗  | ✓* | ✗     | non-comm + non-assoc + conj |
| 3 | Sedenion       | ✗  | ✗  | ✗     | structure only; R3 fail deferred |

`*` = R3 pairwise-generator check formal; full R3 theorem
(universal no-zero-div) deferred (would need Hurwitz four-
square-type identity, substantial polynomial work).

## Key decide-powered proofs

The Cayley non-commutativity and non-associativity were
formally closed by `decide`.  The `decide` tactic computes
both sides of the equation through the CD formula's concrete
pattern-matches and returns `false` for the equality, yielding
the desired `≠` result.

This is a useful technique for CD computations: even though
the full axiom set is not simp-friendly, specific
generator-level witnesses are kernel-decidable.

## Mathematical summary

The Cayley–Dickson tower over the integers

```
  ZI → Lipschitz → Cayley → Sedenion → ...
```

drops *one* Lens-structural axiom per step:
  ℂ-like → (drop R2) → quaternion-like → (drop assoc)
  → octonion-like → (drop R3) → sedenion-like → ...

After the R3 drop, the doubling continues but further
structural axioms keep weakening (alternativity fails at
trigintaduonions = CD^5).  For the Lens framework, the
interesting boundary is **CD layer 0** where R1–R4 all hold.
R4 is admissible further up (CD preserves an involution
forever) but R1–R3 drop one by one as one climbs.

## Deferred

- Sedenion zero-divisor witness (R3 fail, layer 3).
- Lipschitz `mul_assoc` (universal; would need
  quaternion-norm-type identity).
- Lipschitz norm multiplicativity (Hurwitz identity,
  8-variable polynomial).
- CD full characterisation as a "functor" `R4Codomain A →
  (structure, maybe not R4Codomain, on A × A)`.
