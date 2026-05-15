import E213.Term.Internal.Tree
import E213.Term.Internal.Tree.Cmp
import E213.Term.Internal.Tree.Swap
import E213.Term.Internal.Tree.Fold
import E213.Term.Internal.Tree.Levels

/-!
# Term.Tree — public Tree API (re-export shim)

Public surface for the underlying tree machinery used by `Theory.Raw`.
External (above-Term) code should import **this** rather than reaching
into `E213.Term.Internal.Tree*`.

## Exports

- `Tree` — inductive `a | b | slash` (canonical-form scaffold)
- `Tree.cmp`, `Tree.canonical` — order + canonical-form predicate
- `Tree.cmp_*` — lex/swap/eq lemmas (direct, ∅-axiom)
- `Bool.and_eq_true_to_pair`, `Nat213.max_comm` — supporting helpers

## Namespace note

Tree machinery lives under `namespace E213.Term.Internal` — path
aligned with `Term/Internal/Tree*`.  (Pre-2026-05-15 the umbrella
was `E213.Theory.Internal`, a holdover from when Tree.swap /
Tree.fold etc. lived under `Theory/Raw/`; renamed in lockstep
with the move into `Term/Internal/Tree/`.)

## Enforcement (layer discipline)

Per ARCHITECTURE.md (2026-05-12), Theory imports Term API only —
`E213.Term.Internal.*` directly is a layer violation.  The hook
`.claude/hooks/layer-import-guard.sh` (PreToolUse Edit/Write)
catches such imports at write-time.
-/
