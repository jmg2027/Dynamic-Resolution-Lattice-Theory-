# G86 — Self-referential Leibniz of the lex-projection cup

## Status

**Research note.**  2026-05-21.  Generalisation / extension of
G85's "Lens mismatch" finding.  Articulates the **structural
conjecture** that the lex-projection cup's δ obeys a self-
referential Leibniz where the correction term is the cup
*itself* at the middle-removed face.  Empirically verified at
two distinct bidegrees; symbolic proof for general (k, l, n)
deferred.

## The structural identity

For any (n, k, l) with k + l + 1 ≤ n, any α : Cochain n k,
β : Cochain n l, and any (k+l+1)-subset τ of {0..n−1}:

```
δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ (α ⌣ β)(τ \ {τ[k]})
```

The third term is the **boundary-self-correction**: the cup α ⌣ β
evaluated at the face of τ obtained by removing the position-k
vertex (the "boundary" between front-k of τ and back-l of τ).

This is a **self-referential** Leibniz — δ of α ⌣ β at τ involves
the cup itself at a shifted argument.  No external term enters; the
correction is generated from the same algebraic operation that
appears on both sides.

## Why this matters (213-native reading)

Per `seed/AXIOM/05_no_exterior.md` §5, 213 has no exterior;
every operation that *appears* to require external structure
actually closes within the residue.  The lex-projection cup's
Leibniz is an explicit cochain-level instance of this principle:

  · Standard simplicial Alexander-Whitney cup admits a "vanilla"
    Leibniz where δ distributes over ⌣ with no self-reference.
  · ℤ/2 wedge product has its own (vanishing-sign) Leibniz, also
    non-self-referential.
  · **The lex-projection cup is structurally distinct**: its δ
    decomposition leaves a single face un-captured by the
    standard front/back partition of δ — and that uncovered face
    is again a cup value.

In §8 language: the operation's δ behaviour is **internally
closed** — it refers back to itself rather than requiring an
external Leibniz repair.

## Empirical evidence (this session)

### (1, 1) on Δ⁴ — decide-verified across 10240 cases

`lean/E213/Lib/Math/Cohomology/Cup/LeibnizLexSelfRef.lean`:
`lex_cup_leibniz_self_ref_1_1`.  Statement:

  δ(α ⌣ β)(τ) = (δα⌣β)(τ) ⊕ (α⌣δβ)(τ)
              ⊕ (α ⌣ β)(faceMiddleRemoved_5_1_1 τ)

where `faceMiddleRemoved_5_1_1 : Fin 10 → Fin 10` hardcodes the
3-subset → (3-subset minus position-1 vertex) → 2-subset map.

PURE.

### (2, 1) on Δ³ — decide-verified across 1024 cases

`lean/E213/Lib/Math/Cohomology/Cup/LeibnizLex21.lean`:
`lex_cup_leibniz_self_ref_2_1_n4`.  Statement (same form, k = 2):

  δ(α ⌣ β)(τ) = (δα⌣β)(τ) ⊕ (α⌣δβ)(τ)
              ⊕ (α ⌣ β)(faceMiddleRemoved_4_2_1 τ)

PURE.

### Hand-verified (k, l, n) — sample cases

For each of (k, l, n) ∈ {(1, 1, 5), (2, 1, 5), (2, 1, 4)}, several
concrete (α, β, τ) combinations were checked by hand and the
self-referential identity held.  Mismatch with the standard
no-correction Leibniz was confirmed at asymmetric basis pairs
(e.g., α = e_{0,1}, β = e_4 on τ = [0,1,3,4]).

### Deferred — (2, 1) on Δ⁴, (1, 2) on Δ⁴, (2, 2) on Δ⁴

Each requires 2¹⁵-2²⁰ × (face count) decide cases; OOM-ed at
maxHeartbeats 200M with default elaboration.  Smarter
elaboration (or symbolic proof) needed.

## Physical interpretation — speculative

In DRLT's cohomology framework (G35: K_{3,2}^{(c=2)} bipartite
cup-channel structure), cup product between cochains supports
the **channel-counting** semantics across the 8 cohomology
channels at d=5.  The self-referential correction term
`(α⌣β)(τ \ {τ[k]})` is **a cross-channel bridge value**: it
couples the (k+l)-cochain α⌣β to a *lower-dimensional*
representative of itself.

Speculation: if α_em precision residual (5.4×10⁻⁴, per
`research-notes/G35_chiral_cup_ring_catalog.md`) traces back to
cohomology cup products, the **self-reference depth** of the
correction may govern higher-order contributions.  Specifically:

  · Iterated self-reference: δ(α⌣β)(τ) involves (α⌣β)(τ \ {τ[k]}),
    which in turn has its own δ involving more deeply-nested
    face cup values.
  · The α^4 (= α_GUT^(d-1)) suppression structure observed
    in `Couplings/ThetaQCD.lean` and similar files might
    correspond to depth-(d-1) self-reference iteration.

This is conjecture; concrete verification requires translating
the K_{3,2}^{(c=2)} channel cup-product into the lex-projection
formalism.

## ★★★★★ Closure (2026-05-22): ∀ (k, l) PROVED — strict PURE

`lean/E213/Lib/Math/Cohomology/Cup/LeibnizLexListLevel.lean`
contains `list_level_leibniz_general`, a strict-PURE proof of the
symbolic twisted Leibniz at arbitrary (k, l):

  xorRange (k+l+1) (fun i => cupList k l α β (τ.eraseIdx i))
  = xor (xor (cupList (k+1) l (deltaListR k α) β τ)
             (cupList k (l+1) α (deltaListR l β) τ))
        (cupList k l α β (τ.eraseIdx k))

Proven via user's 3-way partition strategy:
  · `xorRange_three_way_partition` — abstract algebraic skeleton
  · `cupList_face_decomp` — per-face structural decomposition
  · `list_level_LHS_partition` — LHS expansion to 3 blocks
  · XOR algebra (AND/XOR distributivity, xorRange (n+1) unfold,
    drop/take boundary lemmas, xorRange_congr for reindexing
    without funext)
  · 4-atom Bool case analysis closes final XOR equality

24 PURE / 0 DIRTY in this file.  No Mathlib, no omega, no funext,
no decide enumeration over (α, β) parameter space.

The remaining work is the Fin-indexed transfer
(`Cohomology/Cup/Core.cup` form) via `subsetIdx ↔ kSubset`
round-trip — substantial structural work, separate from the
algebraic content of this result.

## Original general conjecture (∀ k, l, n)

Stated formally:

```lean
∀ (n k l : Nat), k + l + 1 ≤ n →
∀ (α : Cochain n k) (β : Cochain n l) (τ : Fin (binom n (k+l+1))),
  delta (cup n k l α β) τ
    = xor (xor (cup n (k+1) l (delta α) β τ)
               (cup n k (l+1) α (delta β) τ))
          (cup n k l α β (faceMiddleRemoved n k l τ))
```

where `faceMiddleRemoved n k l : Fin (binom n (k+l+1)) → Fin
(binom n (k+l))` maps τ to the colex index of `τ \ {τ[k]}`.

## Symbolic proof sketch (next session)

The general form admits a structural proof by face decomposition:

  · LHS = δ(α⌣β)(τ) = XOR_{i=0..k+l} (α⌣β)(τ \ {τ[i]})
  · For i ∈ [0..k−1]: face removes a front vertex.  Its
    (α⌣β)-value matches the i-th contribution to δα(τ.take(k+1))
    in (δα⌣β)(τ).
  · For i ∈ [k+1..k+l]: face removes a back vertex.  Its
    (α⌣β)-value matches the (i−k)-th contribution to
    δβ(τ.drop k) in (α⌣δβ)(τ).
  · For i = k: face removes the *boundary* vertex.  This face's
    (α⌣β)-value is **the correction**.

In ℤ/2, all matches XOR to RHS_std + correction = LHS.  Formal
ℓean proof requires inducting on (k+l) or unfolding δ explicitly.
Mathlib-free; achievable via the 213-native `Int213.*` /
`NatHelper` machinery, scoped for the next session.

## See also

  · `research-notes/G85_cup_delta_lens_mismatch.md` — original
    Lens-mismatch framing and resolution path δ.
  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizLex.lean` — initial
    (1, 1) twisted Leibniz with explicit `α(τ[0])·β(τ[last])`.
  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizLexSelfRef.lean` —
    (1, 1) self-referential form via face map.
  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizLex21.lean` —
    (2, 1) on Δ³ confirming generality.
  · `seed/AXIOM/05_no_exterior.md` §5 — doctrinal anchor.
  · `research-notes/G35_chiral_cup_ring_catalog.md` — K_{3,2}^{(c=2)}
    bipartite cup framework where this finding may have physics
    implications.
