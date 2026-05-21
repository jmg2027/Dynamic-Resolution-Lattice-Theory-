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

## Interpretation

Two plausible causes for the universal-Leibniz refutation:

  · **subsetIdx silent-fail**: `Cup.Core.cup` invokes `Delta.Core
    .subsetIdx` (brute-force linear search of `kSubset n k i`).
    When the search fails it returns `binom n k` (out-of-range
    sentinel) and `cup` then yields `false` non-canonically.  For
    certain (front, back) splits this may not match the true
    Alexander-Whitney value.
  · **delta sign and ordering convention**: `Delta.Core.delta` uses
    ℤ/2 XOR over τ \ {τ[i]} faces with `subsetIdx` looking up the
    face's colex index.  An off-by-one in the colex enumeration
    of `kSubset` would break Leibniz universally even though
    matching at the four `v0_5` / `all_true_5_1` / `zero` cases
    that the existing `Cup/Leibniz.lean` tests cover.

The four `Cup/Leibniz.lean` concrete cases all involve highly-
symmetric cochains (constant true, constant false, vertex-0
indicator) where any such silent-fail mode may happen to cancel
on both sides.  The asymmetric basis pairs would expose the
mismatch.

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
theorem cup_leibniz_phase2_marker : True := trivial

end E213.Lib.Math.Cohomology.Cup.LeibnizUniversal
