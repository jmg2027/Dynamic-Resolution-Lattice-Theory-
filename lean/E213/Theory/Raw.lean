import E213.Theory.Raw.API

/-!
# Theory.Raw — compatibility alias

This file re-exports `Theory.Raw.API` for downstream compatibility.
External code should prefer `import E213.Theory.Raw.API` directly
(the explicit public-surface entry point per ARCHITECTURE.md
2026-05-12).

`import E213.Theory.Raw` continues to work; both routes yield the
same public surface.
-/
