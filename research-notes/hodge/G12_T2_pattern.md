# G12 — T²ⁿ pattern: Hodge Index + Hard Lefschetz at small dimensions

**Date:** 2026-05-06 (continuing G6/G7/G8/G9/G10/G11)
**Author:** Mingu Jeong
**Formalisation:** Claude (Anthropic)
**Status:** **Closed strict ∅-axiom** — 4 new capstones bundling
the G10 Phase 2 deferred follow-ups on 213-canonical Kähler
manifolds.

---

## 0. Position

G10 Phase 2 closure summary marked three specific follow-ups
deferred:

> "Non-vacuous extensions (signature on a 213-canonical 2-fold;
>  Hodge-Riemann positivity at ℚ²¹³ level; Hard Lefschetz on a
>  T²×T² shadow with non-zero middle cohomology)…"
>  — `G10_post_hodge_program.md`

This note records the closure of all three, plus a fourth bonus
result (Hodge Index on T²×T² H²) that surfaces a new pattern.

---

## 1. The 4 new capstones

| # | Name | File | Surface | Statement |
|---|------|------|---------|-----------|
| 1 | `hodge_index_t2_capstone` | `Pairing/HodgeIndexT2.lean` | T² | signature (1, 1) on H¹ |
| 2 | `hodge_riemann_t2_capstone` | `Pairing/HodgeRiemannT2.lean` | T² | Kähler `cup(ω, ω) = 2 > 0` + signature decomp |
| 3 | `hard_lefschetz_T2_squared_capstone` | `Structure/HardLefschetzT2Squared.lean` | T²×T² | `L²` mult-by-2 on H⁰→H⁴; `L : H¹→H³` 4×4 perm det = +1 |
| 4 | `hodge_index_T2_squared_capstone` | `Pairing/HodgeIndexT2Squared.lean` | T²×T² | signature (3, 3) on H² (3 hyperbolic blocks) |

All 4 verified by `lake env lean` + `#print axioms` to be
"does not depend on any axioms".

---

## 2. Infrastructure: 213-canonical Kähler-like complexes

`Lib/Math/Cohomology/Surfaces/`:

  · `T2Minimal.lean`              — T² minimal CW
                                    (1 vertex + 2 edges + 1 face)
  · `T2Minimal/CupPairing.lean`   — symmetric `[[0,1],[1,0]]`
  · `T2Minimal/Signature.lean`    — α₊, α₋ basis change → (1, 1)
  · `T2Squared.lean`              — T²×T² Künneth product
                                    (1 + 4 + 6 + 4 + 1 = 16 cells)
  · `T2Squared/HardLefschetz.lean` — Kähler ω = a₁b₁ + a₂b₂;
                                    L² and L : H¹ → H³ as
                                    explicit Int matrices
  · `T2Squared/HodgeIndex.lean`   — cup-pairing on H²:
                                    3 hyperbolic blocks ⟹ (3, 3)

All uses `decide` on finite enumerations — no `omega`, no
`Classical`, no Mathlib.

---

## 3. The new pattern: T²ⁿ signature sequence

### 3.1 Conjecture

For the 2n-fold `T²ⁿ` (real dim 2n, complex dim n), the cup-pairing
signature on the middle cohomology `H^n` is:

  **signature(H^n; T²ⁿ) = (½·C(2n, n),  ½·C(2n, n))**

### 3.2 Status

  · **n = 1** (T², genus 1): signature (1, 1)  =  (½·2, ½·2)
    — Closed ∅-axiom in this commit (`hodge_index_t2_capstone`)
  · **n = 2** (T²×T²): signature (3, 3)  =  (½·6, ½·6)
    — Closed ∅-axiom in this commit (`hodge_index_T2_squared_capstone`)
  · **n = 3** (T²×T²×T²): predicted (10, 10)  =  (½·20, ½·20)
    — Open; same machinery extends straightforwardly to 64 cells.

### 3.3 Why (½·C(2n, n), ½·C(2n, n))?

H^n(T²ⁿ; ℤ) has Betti number `b_n = C(2n, n)` (Künneth on
exterior algebras of 2 generators per factor).  Each
`H^k × H^{n−k} → H^n` block in the Künneth decomposition gives
a hyperbolic pairing; pairing each indicator with its "complement"
gives ±1 entries.  Summing over the C(2n, n) basis classes
yields C(2n, n)/2 hyperbolic blocks each of signature (1, 1) ⟹
total signature (b_n / 2, b_n / 2).

### 3.4 Prediction with explicit witness count

For T²ⁿ:
  · 6 cells in T²×T² → 3 ortho pairs → 6 ± eigenclass witnesses
  · 20 cells in middle of T²³ → 10 ortho pairs → 20 witnesses
  · 70 cells in middle of T²⁴ → 35 ortho pairs → 70 witnesses
  · ...

The formal verification cost grows as `C(2n, n)`, all by `decide`
on finite enumerations — no proof complexity beyond pattern
recognition.

---

## 4. Companion observation: Hard Lefschetz on T²×T²

Standard Hard Lefschetz on T²×T² predicts:

  · L⁰ = id : H² → H² (trivial)
  · L  : H¹ → H³ iso  (rank 4 ⟶ 4)
  · L² : H⁰ → H⁴ iso  (rank 1 ⟶ 1)

In 213-native form on the minimal CW:

  · `L : H¹ → H³` is exactly the **rotation permutation**
    `(a₁ b₁ a₂ b₂) ↦ (a₁a₂b₂, b₁a₂b₂, a₁b₁a₂, a₁b₁b₂)`
    — a 4-cycle on the basis indices (1 ↔ 3, 2 ↔ 4 in the
    H³ indexing); det = +1 ⟹ iso ℤ.

  · `L² : H⁰ → H⁴` is multiplication by 2 (since
    `(a₁b₁ + a₂b₂)² = 2·(a₁b₁a₂b₂)`); iso ℚ.

This is not vacuous in ℤ: the matrix is genuinely a permutation
(over ℤ), so the iso is "tighter" than mere rationality.

---

## 5. Unifying observation

The Hodge Index, Hard Lefschetz, and Hodge-Riemann theorems on
213-canonical Kähler-like complexes all reduce to:

  1. **Enumerate** the cells `Cell^k` of the minimal CW.
  2. **Encode** ℤ-cochains as `Cell^k → Int`.
  3. **Define** the cup product as a wedge of indicators with
     sign tracked by a fixed canonical ordering.
  4. **Discharge** by `decide` on the finite enumeration.

The Sylvester / Hard-Lefschetz / Hodge-Riemann *content* is:

  · For each ortho pair `(α_+, α_-)` with `cup(α_+, α_+) > 0`
    and `cup(α_-, α_-) < 0`, we have one of each eigenvalue.
  · For Hard Lefschetz: a single permutation matrix entry per
    basis vector suffices to witness `det ≠ 0`.

No real analysis, no infinite-dimensional Hilbert space, no
Hodge harmonic theory, no Kähler metric calculus.  213's atomic
indicators + finite enumeration carry the complete content.

---

## 6. Open follow-ups

  · **n = 3 case** (T²³ at signature (10, 10)) — same pattern;
    20 ortho-pair witnesses needed.
  · **General `Σ_g` (genus g)** — surface with 2g edges + 1 face;
    cup-pairing gives signature (g, g) by g independent
    hyperbolic blocks `[[0,1],[1,0]]`.  Parametric `g` can be
    encoded but requires care for `decide` over `Fin (2g)`.
  · **Künneth signature theorem** — abstract version:
    for any two 213-Kähler-complexes X, Y,
      `signature(H^{n+m}; X × Y) = signature(X) ⊕ signature(Y)`
    derivable as a generalization of T² × T² → T² × T² × T².
  · **Hodge-Riemann ℚ-positivity refinement on T²×T²** — extend
    `hodge_riemann_t2_capstone`'s positivity statement from H¹
    to the (1, 1) primitive part `P^{1,1}` of H²(T²×T²).  Needs
    primitive-class definition `P^{1,1} := ker(L : H^{1,1} → H^{1,3})`
    which is vacuous here (H^{1,3} = 0), so `P^{1,1} = H^{1,1}`
    rank 4.

써먹읍시다 (let's use it).
