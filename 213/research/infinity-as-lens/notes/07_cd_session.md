# 07 — CD doubling session 1

Follow-up to notes/03_cayley_dickson.md.  First concrete
Cayley–Dickson construction landed in Lean.

## What was built

### `Research/ZIArith.lean`
Supplement to `ZI`: `Add`, `Neg`, `Sub` instances needed by
CD multiplication.  Also `add_comm`, `conj_neg`, `conj_zero`
and basic componentwise lemmas on `Int`.

### `Research/CDDouble.lean`
The **Lipschitz integer quaternion** as CD doubling of `ZI`:

```
structure Lipschitz where
  re : ZI
  im : ZI

Lipschitz.mul u v :=
  ⟨u.re * v.re - v.im.conj * u.im,
   v.im * u.re + u.im * v.re.conj⟩

Lipschitz.conj u := ⟨u.re.conj, -u.im⟩
```

Theorems:
- `conj_conj`: involutivity.
- `conj_ne_id`: nontrivial involution.
- `I_mul_J`: `I' * J = ⟨0, i⟩`.
- `J_mul_I`: `J * I' = ⟨0, -i⟩`.
- `mul_not_commutative`: `ij = -ji`, so `∃ u v, u*v ≠ v*u`.

## What this says

Cayley–Dickson doubling **exits** the Lens-R4Codomain class:
starting from commutative `ZI`, CD produces a non-commutative
algebra (`Lipschitz` = integer quaternions).  Because
`R12Codomain` requires `combine_comm`, `Lipschitz` is not a
Lens R4Codomain in the paper's R1–R5 sense.

This is the content of the §3.3 failure-witness table row
for "R2 fail via non-commutative combine", upgraded from the
toy `pathLens` example to a genuinely rich algebraic
structure.

## What is NOT yet formalised

- **Norm multiplicativity**: `|uv|² = |u|² · |v|²` through
  octonion level (Hurwitz's theorem).  Requires 8-variable
  polynomial identities; doable with a `quad_norm`-style
  tactic extension.

- **Anti-distributivity of conj**: `conj(u·v) = conj v · conj u`
  (reversed order).  This is the CD version of R4's conj_dist
  (which has same-order multiplication).  The anti-order is
  why CD-doubled algebras are *opposite* R4 conjugates.

- **Further doubling**: Lipschitz → Cayley (octonions), where
  associativity also breaks.  Would need `Lipschitz → Lipschitz`
  product struct; same CD formula.

- **Sedenion step**: Cayley → sedenion, where R3 (no zero
  divisors) breaks.

## Structural summary (R-conditions across the CD tower)

| Level | Integer name | R2 | R3 | assoc | R4-style |
|-------|--------------|----|----|-------|---------|
| 0     | ZI (Gaussian)| ✓  | ✓  | ✓     | ✓       |
| 1     | Lipschitz    | **✗** | ✓ | ✓    | ✓ (anti-dist) |
| 2     | Cayley       | ✗  | ✓  | **✗** | ✓ (anti-dist) |
| 3     | Sedenion     | ✗  | **✗** | ✗  | ✓        |

Each step strictly weakens one axiom while preserving the
involution.  The Lens framework's R1–R5 picks out **level 0**
(ℂ's integer shadow).  CD shows the structural continuation.

## Next

- Extend `quad_norm`-style tactics to 4/8 variables for
  `Lipschitz` norm multiplicativity.
- Second CD layer (`Cayley`) as a `Lipschitz × Lipschitz`
  structure.  Requires the same groundwork: Lipschitz
  arithmetic (Add/Neg/Sub) before CD formula.
