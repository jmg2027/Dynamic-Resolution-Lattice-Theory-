# 01 — Roadmap (Claude's proposal, 2026-04-21)

## Σ series — formal targets

| Id | Statement | Tool | Priority |
|----|-----------|------|----------|
| Σ1 | Raw's generation is finite-symbol | meta (prose) | done by observation |
| Σ2 | ∃ f : Raw → ℕ injective | Gödel encoding on Tree | **high** |
| Σ3 | ∃ g : ℕ → Raw injective | right-leaning tower | **high** |
| Σ4 | Lens image cardinalities span ≥ 1, ℕ, 𝔠 | per-witness | medium |
| Σ5 | ¬ ∃ f : Raw → (Raw → Bool), Surjective | Cantor diagonal | **high** |
| Σ6 | Cantor tower: (Raw → Bool) → Bool uncountable to Raw → Bool | Cantor iterated | medium |
| Σ7 | Cardinality = Lens output (meta) | prose + Σ5 | after Σ5 |

## Session 1 scope (this session)

Implement Σ2, Σ3, Σ5, Σ6 in Lean 4 core under
`framework/E213/Infinity/`:

- `Infinity/Countable.lean` — Σ2, Σ3 (Raw ≈ ℕ).
- `Infinity/Cantor.lean` — Σ5 directly on Raw.
- `Infinity/Tower.lean` — Σ6 two-layer.

These four theorems give the "mathematicians'
understanding-level" evidence Mingu asked for.

## Session 2 scope (planned)

- Σ4 in full: show explicit Lens → image cardinality table.
- Σ7 written up carefully as a meta-statement.
- Cayley–Dickson connection (separate note 03).

## Pushback / known limits

- Lean 4 core has no `Cardinal` type; cardinality claims
  are done via `Function.Injective` / `Surjective` only.
- Uncountable = "no surjection ℕ → X" in this framework,
  which is enough for Cantor-level claims but not for
  exotic large cardinals.
- "Hyper-infinity" in the original thesis can mean either
  (a) up through `2^(2^ℕ)` (achievable via iterated
  function space) or (b) large cardinals (needs
  set-theoretic apparatus; out of scope).
- We settle for (a) — "up to what a mathematician reads
  without specialised set-theoretic machinery".
