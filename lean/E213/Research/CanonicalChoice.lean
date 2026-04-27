import E213.Firmware.Raw

/-!
# Research.CanonicalChoice: canonical-form selection 이 internal
choice function

PAPER1 §4.5 (encoding-artifact independence) 의 deeper
formalization: Raw.slash 의 canonicalization (Tree.cmp lex
order 의 smaller-first selection) 이 *constructive
representative selector*.  ZFC Choice 가 representative
selection 으로 쓰이는 setting 에서 213 은 canonical form 으 로
대체.

## 의의

- Raw.slash x y h 가 deterministic — exactly one of (x.val,
  y.val) 또 는 (y.val, x.val) 이 canonical order, 따라서
  canonical Tree 가 unique.
- 이 selection 이 axioms 부재.
- Raw.slash_comm 이 symmetric input → same output: choice
  function 의 well-defined-on-quotient property.
-/

namespace E213.Research.CanonicalChoice

open E213.Firmware
open E213.Firmware.Internal

/-- **Canonical-form selection 의 trichotomy**: distinct
    `x, y : Raw` 에 대해 exactly one of (lt, gt) holds.  즉
    Raw.slash 의 canonical 결정 이 always definite, 어떤
    representative selection 도 명시적. -/
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

end E213.Research.CanonicalChoice
