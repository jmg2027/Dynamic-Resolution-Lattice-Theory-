import E213.Term.Internal.Tree
import E213.Term.Internal.Tree.Cmp

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

Tree machinery lives under `namespace E213.Theory.Internal`
(Internal-shared umbrella, ARCHITECTURE.md naming exceptions —
retained to avoid mass-renaming 56+ downstream references).
Path-namespace mismatch is intentional.

## Enforcement (layer discipline)

Per ARCHITECTURE.md (2026-05-12), Theory imports Term API only —
`E213.Term.Internal.*` directly is a layer violation.  The hook
`.claude/hooks/layer-import-guard.sh` (PreToolUse Edit/Write)
catches such imports at write-time.
-/
