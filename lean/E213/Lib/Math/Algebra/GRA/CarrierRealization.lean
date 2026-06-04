import E213.Lib.Math.Algebra.GRA.LensBridge
import E213.Lib.Math.Algebra.GRA.Enrichment

/-!
# GRA Carrier Realization — Phase 17 (post-consolidation)

Phase 16's `LensBridge` showed the (single, post-consolidation)
enrichment grade map is definitionally equal to
`canonicalGradeMap := Raw.fold 2 3 (· + ·)` at the Nat level.
The carrier-level full equation
`Raw.fold (BipartiteCarrier.two) (BipartiteCarrier.three)
          BipartiteCarrier.combine r` ↔ `canonicalGradeMap r`
would require PURE `combine_sym` on the enriched type with its
`Prop` constraint field, which is fragile.

This file bypasses that by the **direct realization** approach.
Key observation: `canonicalGradeMap r ≥ 2` for every `r : Raw`
(atoms map to 2 or 3; slash adds two ≥-2 values to give ≥ 4).
We can therefore construct `Raw → BipartiteCarrier` directly:

```
bipartiteRealize r := ⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩
```

— bypassing `Raw.fold` on the enriched carrier entirely.  The
grade-projection `(bipartiteRealize r).n = canonicalGradeMap r`
is `rfl`.

After consolidation, the former five domain-flavoured
realizations (`walkRealize`, `cochainRealize`, ...) collapse to a
single `bipartiteRealize` — they were rfl-equal anyway.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.CarrierRealization

open E213.Theory
open E213.Lib.Math.Algebra.GRA.LensBridge
open E213.Lib.Math.Algebra.GRA.Enrichment (BipartiteCarrier)

/-! ### §1 — The key lemma: `canonicalGradeMap r ≥ 2` for every Raw -/

/-- Every Raw has canonical grade ≥ 2.  Atoms give 2 or 3
    directly; slash gives a sum of two ≥-2 values, hence ≥ 4. -/
theorem canonical_ge_2 (r : Raw) : canonicalGradeMap r ≥ 2 := by
  induction r using Raw.rec with
  | a => exact Nat.le.refl
  | b => exact Nat.le.step Nat.le.refl
  | slash x y h ihx _ihy =>
    rw [canonicalGradeMap_slash x y h]
    exact Nat.le_trans ihx (Nat.le_add_right _ _)

/-- `canonical_ge_2` packaged as the disjunction the enrichment
    requires. -/
theorem canonical_constraint (r : Raw) :
    canonicalGradeMap r = 0 ∨ canonicalGradeMap r ≥ 2 :=
  Or.inr (canonical_ge_2 r)

/-! ### §2 — The direct enriched realization

Built by pairing `canonicalGradeMap` with the constraint proof
from §1.  No `Raw.fold` on the enriched carrier is used.
-/

/-- Bipartite realization: `Raw → BipartiteCarrier`.  Replaces
    the former five domain-flavoured realizations (`walkRealize`,
    `cochainRealize`, `truncationRealize`, `operadRealize`,
    `resolutionRealize`) — all five were definitionally equal. -/
def bipartiteRealize (r : Raw) : BipartiteCarrier where
  n := canonicalGradeMap r
  constraint := canonical_constraint r

/-! ### §3 — Grade-projection (= `canonicalGradeMap` by `rfl`) -/

/-- The grade-projection equals `canonicalGradeMap`. -/
theorem bipartiteRealize_n (r : Raw) :
    (bipartiteRealize r).n = canonicalGradeMap r := rfl

/-! ### §4 — Atom and slash behaviour of the realization -/

theorem bipartiteRealize_a : (bipartiteRealize Raw.a).n = 2 := rfl
theorem bipartiteRealize_b : (bipartiteRealize Raw.b).n = 3 := rfl

/-- Realization respects slash: the underlying value is additive. -/
theorem bipartiteRealize_slash (x y : Raw) (h : x ≠ y) :
    (bipartiteRealize (Raw.slash x y h)).n =
    (bipartiteRealize x).n + (bipartiteRealize y).n :=
  canonicalGradeMap_slash x y h

end E213.Lib.Math.Algebra.GRA.CarrierRealization
