import E213.Theory.Raw

/-!
# CanonicalChoice: canonical-form selection as an internal
choice function

Deeper formalization of PAPER1 §4.5 (encoding-artifact independence):
The canonicalization of Raw.slash (smaller-first selection under
Tree.cmp lex order) is a *constructive representative selector*.
In settings where ZFC Choice is used for representative selection,
213 replaces it with canonical form.

## Significance

- Raw.slash x y h is deterministic — exactly one of (x.val, y.val)
  or (y.val, x.val) is in canonical order, so the canonical Tree
  is unique.
- This selection requires no axioms.
- Raw.slash_comm maps symmetric input → same output: the
  well-defined-on-quotient property of a choice function.
-/

namespace E213.Lib.Math.Choice.Canonical

open E213.Theory
open E213.Theory.Internal

/-- **Trichotomy of canonical-form selection**: for distinct
    `x, y : Raw`, exactly one of (lt, gt) holds.  That is,
    the canonical decision for Raw.slash is always definite,
    and any representative selection is explicit. -/
theorem canonical_trichotomy (x y : Raw) (h : x ≠ y) :
    Tree.cmp x.val y.val = .lt ∨ Tree.cmp y.val x.val = .lt := by
  match hc : Tree.cmp x.val y.val with
  | .lt => exact Or.inl rfl
  | .gt =>
      have hlt : Tree.cmp y.val x.val = .lt :=
        (Tree.cmp_gt_iff_lt_swap x.val y.val).mp hc
      exact Or.inr hlt
  | .eq =>
      exfalso
      exact h (Subtype.ext ((Tree.cmp_eq_iff _ _).mp hc))

end E213.Lib.Math.Choice.Canonical
