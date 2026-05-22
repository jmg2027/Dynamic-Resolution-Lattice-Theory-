# G123 — Lens-recipe cup catalog: δ-closure laws from count-Lens recipes

## Status

**Research direction.**  2026-05-22.  Spawned directly by G86 closure
(`research-notes/G86_self_referential_lex_cup_leibniz.md`).
Comprehensive program; broken into A→F sub-directions below.

**A.1-A.3 LIST LEVEL: CLOSED (2026-05-22)** — catalog dispatch theorem
in `lean/E213/Lib/Math/Cohomology/Cup/LeibnizCatalog.lean` packages
the recipe ↔ δ-closure correspondence for the three single-partition
recipes (lex, mirror, sym).  8 new strict-PURE theorems across 3 new
files (`LeibnizMirror`, `LeibnizSym`, `LeibnizCatalog`).

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

| # | Recipe | Cup | δ-closure (list level) | Status |
|---|---|---|---|---|
| 1 | sorted-single-partition (ascending, s=k) | `cup` (lex-projection) | self-ref at `τ.eraseIdx k` | **PROVED — `list_level_leibniz_general` (G86)** |
| 2 | all-partitions, ℤ/2 sign | wedge `α ∧ β` | no correction (sign vanish) | KNOWN (external) |
| 3 | sorted-single-partition (s=l, mirror) | `cupRev α β` = `cup l k β α` (swap) | self-ref at `τ.eraseIdx l` (mirror) | **PROVED — `list_level_leibniz_mirror`** |
| 4 | middle-out (split at `s ∉ {k, l}`) | (degenerate type signature) | — | INADMISSIBLE (lengths mismatch) |
| 5 | anti-symmetric ℤ/2 wedge of 2 cochains | (degenerate) | vanish on Bool | TRIVIAL |
| 6 | XOR-symmetrised (α⌣β ⊕ β⌣α) | `cupSymList` | XOR of corrections at k and l | **PROVED — `list_level_leibniz_sym`** |

**Catalog finiteness theorem**: Rows 1, 3, 6 exhaust the
admissible count-Lens-canonical sorted-single-partition recipes.
For sorted lists τ of length k+l, the split position `s` must
satisfy `s = k` (α to front) or `s = l = (k+l) - k` (α to back).
Row 6 is the only XOR-symmetrisation of rows 1 and 3.  No further
admissible single-partition recipe exists.

The catalog is finite (the count-Lens choices on a (k+l)-subset are
enumerable — pick a partition rule for sorted lists).

### B. Self-reference depth → α^(d-1) suppression (physics) — **PROTOTYPE (2026-05-22)**

If face-iteration depth `d-1` matches `α_GUT^(d-1) = α^4` suppression
empirically observed (ThetaQCD, α_em higher-order), G86 self-ref
correction would give a **zero-parameter physics prediction**.

Prototype done — see `lean/E213/Lib/Math/Cohomology/Cup/SelfRefDepth.lean`:

  · `selfRefIter (k l α β) (depth : Nat) (τ : List Nat) : List Bool` —
    iteratively drop the k-th vertex of the current face, recording
    `cupList k l α β` at each step.  Output length = depth.  PURE.
  · `depth4Sig α β := selfRefIter 1 1 α β 4 [0, 1, 2, 3, 4]` — the
    DRLT-aligned depth-(d-1) signature on Δ⁴.
  · `α_e i` = single-vertex indicator cochain.

**Structural finding** (`basisDepth4Sig_unique_survivor`):
Across all `5 × 5 = 25` indicator basis pairs `(α_e i, α_e j)`
on Δ⁴ at split position 1, **exactly one pair** — `(0, 4)` —
survives the depth-4 face-iteration with a non-zero signature
bit (and that bit is the last, depth-3 entry):

```
basisDepth4Sig 0 4 = [false, false, false, true]
basisDepth4Sig i j = [false, false, false, false]   for (i, j) ≠ (0, 4)
```

The unique survivor `(0, 4)` is the **boundary-endpoint pair**
(minimum-vertex × maximum-vertex of Δ⁴).  The depth-4 saturation
ratio is `1/25 = 0.04` — a count-Lens output.

Interpretation: at d = 5, the cup self-reference depth-(d-1)
iteration **uniquely selects the boundary-diameter channel** of
the simplex.  This single surviving channel is a candidate for
the **leading α^(d-1) = α^4 suppression contribution** in DRLT
physical constants.

**Bidegree-to-depth correspondence** (extended catalog):

| Bidegree (k, l) | Specific (α, β) | Firing depth bit | Codimension |
|---|---|---|---|
| (1, 1) | `(α_e 0, α_e 4)`           | 3 | 3 |
| (1, 2) | `(α_e 0, β_e2 3 4)`        | 2 | 2 |
| (1, 3) | `(α_e 0, β_e3 2 3 4)`      | 1 | 1 |

Pattern: at split position 1 on the full Δ⁴ initial τ, the firing
depth of an `(α_e 0, β_eN i₁ … iₗ)` configuration is `d - 1 - l`
(where d = 5).  This **IS** the codimension of the β-support face
in Δ⁴: a length-l indicator face has codim `d - 1 - l = 4 - l`.

So the depth-bit position of the firing **equals** the codimension
of the β-support face.  The cup self-reference depth is a direct
count-Lens output of the codim hierarchy.

The boundary-endpoint pair `(α_e 0, α_e 4)` (l = 1, codim 3)
sits at the deepest end — the **canonical depth-(d-1) saturation
channel**.

15 new strict-PURE theorems in `SelfRefDepth.lean`.

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

## Done (2026-05-22)

1. Defined `cupRev` (reverse-lex), proved `cupRev_eq_cup_swapped`
   (value equality with `cup l k β α` after Fin re-typing).  PURE.
2. Stated and proved `list_level_leibniz_mirror` as direct 1-line
   corollary of `list_level_leibniz_general` at swapped `(l, k)`
   bidegree.  PURE.
3. Defined `cupSymList` (XOR symmetrisation) and proved
   `list_level_leibniz_sym` — the doubled-correction Leibniz of
   the symmetric cup.  PURE.
4. Packaged the catalog as a single dispatch theorem
   `catalog_dispatch (r : Recipe k l)` over an inductive `Recipe`
   data type (`.lex / .mirror / .sym`).  PURE.
5. Catalog finiteness argued in §"Catalog finiteness theorem"
   above (sorted-single-partition admissibility forces s ∈ {k, l}).

8 new strict-PURE theorems across 3 new files:
  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizMirror.lean`
  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizSym.lean`
  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizCatalog.lean`

## Open frontier

- Fin-level transfer of `catalog_dispatch` (analogous to G86's
  `fin_level_leibniz_general` for row 1).  Mechanical replication
  of G86 machinery with k ↔ l swap for row 3; XOR-of-two-G86 for
  row 6.  Deferred — list-level dispatch suffices for downstream
  physics applications.
- Sub-directions B (depth → α^(d-1) suppression), C (channel κᵢ
  derivation), E (cup-atomic subalgebra), F (p-adic confluence).

## See also

  · `research-notes/G86_self_referential_lex_cup_leibniz.md` — origin.
  · `theory/math/cohomology/cup.md` — cup chapter (current).
  · `seed/AXIOM/05_no_exterior.md` §5 — doctrinal anchor.
  · `research-notes/G35_chiral_cup_ring_catalog.md` — K_{3,2}^{(c=2)}.
