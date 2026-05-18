# Architecture — layered mirror of `lean/E213/`

## Principle

Rust is *not* a fast paraphrase of Lean.  Rust is a **second
implementation of 213** whose every runtime path is a re-execution
of a Lean-proven definition.  Trust flows one direction:

```
Rust  ─(certificate, ℚ-pair JSON)→  Lean checker  →  0-axiom verdict
```

Lean never imports Rust.  Rust never declares theorems.

## Layer map (Lean → Rust)

| Lean | Rust crate | Role |
|------|-----------|------|
| `Term/Term, Compare, Pair, Rat, …` | `term/` | ℕ encoding, decidability, ℚ-as-(ℕ,ℕ), normal form |
| `Theory/Raw*` | `theory/` (raw mod) | `Raw` opaque + `slash`/`fold`/`swap` API |
| `Lens/` | `theory/` (lens mod) + `lens/` | sealed `Lens<A>`, canonical instances, K_{3,2}^{(2)} |
| `Theory/Atomicity, Pigeonhole, …` | `theory/atomicity/` (atomicity, arity) | Atomicity, NonDecomposable, ArityForcing |
| `Lib/Math/Analysis/*` | `theory/atomicity/` (analysis213) | Cut algebra, dyadic, derivative, integral — algorithm form |
| `Lib/Math/Cohomology/*` | `lens/` (cohomology) | δ², ⋆⋆, fluxes — as Lens compositions |
| `App/Simplex` + `Physics/AlphaEM*` | `app/` | Concrete 213 objects, observables, brackets |

Note: cohomology is in Lean's `Math/` but conceptually sits between
Lens and computation.  Rust places it adjacent to Lens since
cohomology operations *are* Lens compositions.

## Crate dependency DAG (compile-enforced)

```
                term
                  ↑
                theory
                  ↑
              lens
                  ↑
                  os
                  ↑
                 app
```

`Cargo.toml` `[dependencies]` only allows lower → higher.  A reverse
edge fails `cargo build`.  This mirrors `lean/E213/` import order
(`Theory` cannot import `Lens`, etc. — per
`lean/E213/ARCHITECTURE.md`).

## Why this layering

- **Encapsulation:** each crate exposes only what its Lean
  counterpart exposes.  `Tree` (Raw's internal) is `pub(crate)` —
  invisible above theory, just as Lean's `Internal` namespace.
- **Citation locality:** an op in `app/` can only cite Lean theorems
  whose imports are reachable from `App/`.  No cross-layer cheating.
- **Lazy growth:** OS's `analysis213` module starts empty.  Each new
  algorithm enters only when an `app/` calculation requires it.
  No 268-def upfront port.
