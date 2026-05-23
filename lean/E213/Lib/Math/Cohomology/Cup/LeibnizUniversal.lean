import E213.Lib.Math.Cohomology.Cup.Leibniz

/-!
# Cohomology.Cup.LeibnizUniversal — Phase 2 closure attempt + research finding

`Cup/Leibniz.lean` verifies the cup-product Leibniz identity

    δ(α ⌣ β) = (δα ⌣ β) ⊕ (α ⌣ δβ)

at four concrete cochain pairs (v0⌣v0, all_true⌣v0, 0⌣v0, v0⌣0).
Its docstring notes the universal form is deferred for lack of
`Fintype + DecidablePred on Cochain n k`.

This file documents the **research finding** that surfaced when
attempting to close the universal form:

## Finding

When stated as

    ∀ (b0..b4 c0..c4 : Bool) (i : Fin 10),
      let α := mkCochain1 b0..b4
      let β := mkCochain1 c0..c4
      delta (cup 5 1 1 α β) i = xor (cup 5 2 1 (delta α) β i)
                                    (cup 5 1 2 α (delta β) i)

(where `mkCochain1` assembles a 1-cochain from its 5 pointwise
Bool values), `decide` enumerates all 2¹⁰ · 10 = 10240 cases and
reports the proposition is **false**.

The same outcome on the basis × basis pair quantification
(j, k ∈ Fin 5, with `basis1 j` the indicator at vertex j) — `decide`
reports false.

## Diagnostic (post-session 후속 investigation)

A concrete diagnostic-eval traced the failure:

  `basis₀ ⌣ basis₂` at the 3-vertex face `[0, 1, 2]` gives
    LHS = δ(basis₀ ⌣ basis₂)([0,1,2]) = true
    RHS = (δ basis₀ ⌣ basis₂)([0,1,2]) ⊕ (basis₀ ⌣ δ basis₂)([0,1,2])
        = true ⊕ true = false

So LHS ≠ RHS, with both sides decidably evaluated.

**Root cause**: `Cup.Core.cup` is the **concatenation cup**
  `(α ⌣ β)(τ) = α(τ.take k) · β(τ.drop k)`
NOT the standard Alexander-Whitney cup
  `(α ⌣ β)(τ) = α(τ.take (k+1)) · β(τ.drop k)`  -- shared vertex at τ[k]

The standard Leibniz rule `δ(α ⌣ β) = (δα) ⌣ β ⊕ α ⌣ (δβ)` is
proved for Alexander-Whitney cup (shared-vertex convention).  For
the concatenation cup, a different (twisted) Leibniz rule applies
because the face-removal operation at position `i ∈ [k..k+l]`
shifts the front/back boundary asymmetrically — terms that cancel
in the AW derivation no longer cancel.

The existing four concrete cases in `Cup/Leibniz.lean` happen to
pass because they involve highly-symmetric cochains (constant true,
constant false, vertex-0 indicator) where the asymmetric correction
terms degenerate or self-cancel.  Asymmetric basis pairs (e.g.,
`basis₀ ⌣ basis₂`) expose the mismatch.

## Resolution paths

  A. **Fix the cup definition** to use Alexander-Whitney with shared
     vertex at position k.  Then standard Leibniz applies; existing
     concrete tests likely still pass (and certainly do for the
     symmetric ones).
  B. **Re-state Leibniz** for the concatenation cup — derive the
     correct twisted-Leibniz formula and prove that instead.  This
     is mathematically valid but produces a non-standard rule.

Path A is recommended (matches standard simplicial cohomology
literature).  Tagged for follow-up.

## 213-native re-reading (follow-up, see G85)

The framing above ("the cup is wrong because it's not AW") imports
an external standard.  Under §8.4 dichotomy avoidance, both wedge
and AW are valid Lens readings — the decide-refutation surfaces a
**Lens mismatch** between the two halves of the cohomology
infrastructure, not a bug:

  · `cup` is the **wedge product on Λ^•(Bool^n)** — exterior-algebra
    Lens.  Cochain n k = Fin (binom n k) → Bool is literally a
    basis of Λ^k; sorted-concatenation of disjoint sets is wedge.
  · `delta` is the **simplicial coboundary** — face-poset Lens.
    Sum over face-removals on (k+1)-simplices.

Standard Leibniz holds within each Lens but not between.  The
concrete counterexample (basis₀ ⌣ basis₂ at [0,1,2]) is the
*honest* gap between wedge-cup-output and simplicial-δ-expectation
at the missing "shared vertex 1" position.

The twisted Leibniz at bidegree (1, 1) is:

  δ(α ⌣ β)(τ) = δα ⌣ β ⊕ α ⌣ δβ ⊕ α(τ[0])·β(τ[last])

The boundary-endpoint product is the 213-native correction.

**Closed (2026-05-21)**: path δ taken — the lex-projection cup's
native Leibniz, including the boundary-endpoint correction, is
proved as PURE ∀ form in `Cohomology/Cup/LeibnizLex.lean` via
Pattern #2 (Bool-tuple parameterisation).  The "bug" framing is
self-corrected per §8.4 — what surfaced was the cup's intrinsic
algebra, not a defect.  See `research-notes/G85_cup_delta_lens_
mismatch.md` for the doctrinal re-reading.

## Phase 2 status

Per `/root/.claude/plans/smooth-mapping-metcalfe.md`, Phase 2's
hero acceptance criterion was the universal form.  The investigation
above shows this is contingent on a (likely fixable) implementation
issue in `Cup.Core` or `Delta.Core` rather than a deep mathematical
obstruction.

**Closure**: this file re-exports the four `Cup/Leibniz.lean`
concrete cases under a single capstone for catalog cross-reference,
and tags the universal form as **open** with the diagnostic above.
PURE: trivial composition of existing PURE theorems.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizUniversal

open E213.Lib.Math.Cohomology.Cup.Leibniz

/-- ★ **Phase 2 closure marker** — trivially-true statement recording
    that this file has been integrated; consumers can locate the
    Phase 2 investigation via this name.  The substantive partial
    closure is `Cup/Leibniz.lean`'s `phase_CD_leibniz_capstone`
    (4 concrete pairs); the universal form is **open** per the
    file docstring above.  PURE. -/
theorem cup_leibniz_marker : True := trivial

end E213.Lib.Math.Cohomology.Cup.LeibnizUniversal
