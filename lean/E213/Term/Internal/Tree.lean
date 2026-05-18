/-!
# Term.Internal.Tree — ordered tree scaffolding for Raw

The underlying inductive `Tree` and ordering machinery
(`Tree.cmp`, `Tree.canonical`) for Raw's canonical-form subtype.

**Layer**: Term ring per ARCHITECTURE.md (2026-05-12) — "Raw 의
구현체 (Tree 등)".  Theory imports this via its public path
`Term.Internal.Tree` to define `Raw := {t : Tree // ...}`.

**Namespace**: `E213.Term.Internal` — path-aligned (2026-05-15).
Previous umbrella `E213.Theory.Internal` (kept while Tree.swap /
Tree.fold etc. were still housed under `Theory/Raw/`) was renamed
in lockstep with the move into `Term/Internal/Tree/`.
-/

namespace E213.Term.Internal

inductive Tree : Type
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree
  deriving DecidableEq, Repr

protected def Tree.cmp : Tree → Tree → Ordering
  | .a,         .a         => .eq
  | .a,         .b         => .lt
  | .a,         .slash _ _ => .lt
  | .b,         .a         => .gt
  | .b,         .b         => .eq
  | .b,         .slash _ _ => .lt
  | .slash _ _, .a         => .gt
  | .slash _ _, .b         => .gt
  | .slash x₁ y₁, .slash x₂ y₂ =>
      match Tree.cmp x₁ x₂ with
      | .eq => Tree.cmp y₁ y₂
      | .lt => .lt
      | .gt => .gt

protected def Tree.canonical : Tree → Bool
  | .a         => true
  | .b         => true
  | .slash x y =>
      x.canonical && y.canonical &&
      (match Tree.cmp x y with | .lt => true | _ => false)

end E213.Term.Internal
