# G123 — Lens-recipe cup catalog: δ-closure laws from count-Lens recipes

## Status

**Research direction.**  2026-05-22.  Spawned directly by G86 closure
(`research-notes/G86_self_referential_lex_cup_leibniz.md`).
Comprehensive program; broken into A→F sub-directions below.
Sub-direction **A** is being executed first.

## Motivation

G86 closed the Fin-level ∀(n, k, l) twisted Leibniz for the
**lex-projection cup**:

```
δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ (α ⌣ β)(τ \ {τ[k]})
```

The correction `(α ⌣ β)(τ \ {τ[k]})` is **self-referential** — δ of
α⌣β refers back to α⌣β's own face value, no external term enters.

The lex-projection cup was chosen because:

  · Sorted partition is the count-Lens-canonical form (single
    partition per (k+l)-subset, no choice).
  · The "middle vertex" `τ[k]` is the count-Lens-distinguished
    position (the unique split point).
  · The δ-correction at this middle vertex is the operation's
    **internal closure** — per `seed/AXIOM/05_no_exterior.md` §5,
    every operation that appears to need external structure
    actually closes within the residue.

**Question**: What are the OTHER count-Lens recipes for building a
cup product, and what δ-closure law does each produce?

Standard math has only the Alexander–Whitney cup (vanilla Leibniz)
and the ℤ/2 wedge (sign-vanishing, no correction).  Both lack the
counter-Lens-recipe vocabulary that 213 has.  The recipe-to-closure
map is **a 213-native algebraic structure**: it catalogues *which
cochain-level operations close internally* under which face-removal
boundary behaviour.

## Sub-directions

### A. Lens-recipe → δ-closure catalog (THIS NOTE'S FOCUS)

Build the recipe-to-closure 4-tuple catalog.  Each row = one Lens
recipe → one cup definition → one δ-closure law → one Lean theorem.

| # | Recipe | Cup | δ-closure | Status |
|---|---|---|---|---|
| 1 | sorted-single-partition (ascending) | `cup` (lex-projection) | self-ref at `τ[k]` | **PROVED (G86)** |
| 2 | all-partitions, ℤ/2 sign | wedge `α ∧ β` | no correction (sign vanish) | KNOWN |
| 3 | sorted-single-partition (descending) | `cupRev` (reverse-lex) | self-ref at `τ[l]` (mirror) | **CONJECTURE (A.3)** |
| 4 | middle-out (split-at-pivot) | `cupMid` | unknown | OPEN |
| 5 | anti-symmetric ℤ/2 wedge of 2 cochains | (degenerate) | vanish on Bool | TRIVIAL |
| 6 | bidegree-symmetric (α⌣β + β⌣α) / 2 | `cupSym` | doubled correction (cancels in ℤ/2) | **CONJECTURE (A.4)** |

The catalog is finite (the count-Lens choices on a (k+l)-subset are
enumerable — pick a partition rule for sorted lists).

### B. Self-reference depth → α^(d-1) suppression (physics)

If face-iteration depth `d-1` matches `α_GUT^(d-1) = α^4` suppression
empirically observed (ThetaQCD, α_em higher-order), G86 self-ref
correction would give a **zero-parameter physics prediction**.

Prototype:
  · `selfRefIter (α β τ) : List Bool` — start at τ (length k+l+1),
    iterate: drop middle vertex of current face, record cup value.
  · Path terminates at empty face (length 0).
  · For τ of length k+l+1, max depth = k+l+1.  At d=5 this is ≤ 5.
  · Compare depth-4 signature to α^4 coefficient in physical
    constants.

DRLT Validation Standard #1 (strict ∅-axiom precision theorem at
ppb-ppm) candidate.

### C. Cup-channel κᵢ structural derivation (zero-parameter)

DRLT Closure Form `obs = R · Π(1 + κᵢ · αᵢ^nᵢ)` has channel weights
κᵢ currently fit empirically.  G35 identifies 8 channels at
K_{3,2}^{(c=2)} on d=5.

**Hypothesis**: G86 self-ref Leibniz constrains κᵢ structurally.
The face-map `τ ↦ τ\{τ[k]}` couples channels (i, j) by a specific
0/1 matrix derivable from cup-bidegree structure.  Spectral
analysis of this coupling matrix should yield κᵢ exactly.

If validated: tightens or eliminates the 5.4×10⁻⁴ α_em residual.

### D. Reverse-lex cup mirror (1 session)

`cupRev` = reverse-lex variant, defined symmetrically.  Mirror
Leibniz with correction at `τ[l]` instead of `τ[k]`.  Sub-row of
catalog A.  Direct corollary of G86's machinery — trivial follow-up.

### E. Cup-atomic subalgebra classification

`cup_atomic` cochains: those α, β where `α ⌣ β = α ⌣ β(τ \ {τ[k]})`
for all τ — i.e., translation-invariant in face position.  Closed
under δ via self-ref Leibniz (correction is trivial).  d=5 dimension
count of cup-atomic cochains per bidegree.

### F. p-adic cup ring (G122 confluence)

G122 builds ℤ_p PURE.  Lift cochains over F_p to cochains over ℤ_p,
verify self-ref Leibniz holds at p-adic precision.  5-adic
specialisation aligns with `N_U = 5²⁵`.  Natural confluence with
G122 Phase 6.

## Priority and ordering

A (this note, in progress) → D (1-session corollary inside A) →
E (subalgebra) → B (physics prototype) → C (channel κᵢ if B
positive) → F (G122 confluence).

## A: Lens-recipe catalog — detailed plan

### A.1.  Recipe definitions (PURE, ∀(n, k, l))

For each recipe, define the cup as a `Cochain n k → Cochain n l →
Cochain n (k+l)` function and prove the basic algebraic properties
(zero on either side gives zero, etc.):

  · `cup` (already done) — front k vertices in sorted order, back l.
  · `cupRev` — back k vertices in sorted order, front l (mirror).
  · `cupMid` — split at the middle position `⌊(k+l)/2⌋`.
  · `cupSym` — `α ⌣ β ⊕ β ⌣ α` (Bool XOR symmetrisation).

### A.2.  δ-closure laws

For each recipe, derive its δ-closure.  Likely shapes:

  · `cupRev`: `δ(α ⌣ᴿ β) = δα ⌣ᴿ β ⊕ α ⌣ᴿ δβ ⊕ (α ⌣ᴿ β)(τ \ {τ[l]})`
  · `cupMid`: correction at `τ[⌊(k+l)/2⌋]`.
  · `cupSym`: doubled correction cancels in ℤ/2 → vanilla Leibniz
    when α, β bidegree-symmetric.  Otherwise, sum of two corrections.

### A.3.  Recipe equivalence classes

Two recipes give the "same" cup when they agree on all bidegrees;
otherwise they're algebraically distinct.  Catalogue the equivalence
classes.  Hypothesis: the equivalence classes are indexed by the
count-Lens "split position" function `(k+l) → {0..k+l-1}`, which
is a discrete finite set — confirming the catalog's finiteness.

### A.4.  Comparison theorem

Final capstone for A: a single Lean theorem stating

```lean
theorem lens_recipe_cup_catalog_general :
    ∀ (recipe : SortedPartitionRecipe), exists corrPosition,
      ∀ (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
        (τ : Fin (binom n (k+l+1))),
        delta (cupOf recipe α β) τ = ...std⊕(cupOf recipe α β)(face_at corrPosition τ)
```

The catalog is THE single "every count-Lens recipe gives a self-
referential Leibniz at its split position" theorem — a 213-native
**no-exterior** principle made concrete at the cochain level.

## Next steps (THIS SESSION)

1. Define `cupRev` (reverse-lex), prove basic algebraic properties.
2. State the mirror Leibniz for `cupRev`.
3. Prove via mirror-image of the G86 proof structure.
4. Catalogue `cupMid` definition (proof deferred).

## See also

  · `research-notes/G86_self_referential_lex_cup_leibniz.md` — origin.
  · `theory/math/cohomology/cup.md` — cup chapter (current).
  · `seed/AXIOM/05_no_exterior.md` §5 — doctrinal anchor.
  · `research-notes/G35_chiral_cup_ring_catalog.md` — K_{3,2}^{(c=2)}.
