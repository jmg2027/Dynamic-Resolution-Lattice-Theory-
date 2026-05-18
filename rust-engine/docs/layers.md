# Layers — per-crate responsibilities

## `term/` — ℕ encoding + decidability

Mirrors `lean/E213/Kernel/`.  No physical content; pure
combinatorial substrate.

- `term.rs` — `Term` (ℕ inductive: `zero`, `succ`, `add`, `mul`).
  Direct mirror of `Kernel/Term.lean`.  Backed by `BigUint`.
- `compare.rs` — `le_b`, `equiv` (Bool).  Mirror of `Kernel/Compare`.
- `pair.rs` — pair encoding.  Mirror of `Kernel/Pair`.
- `rat.rs` — `equivQ`, `leQ` (cross-mul).  Mirror of `Kernel/Rat`.
  **No `Q.add` / `Q.mul`.**  Carry rationals as `(BigUint, BigUint)`.
- `normal_form.rs` — `Monomial { p, q }` for `x^p y^q` canonical
  form.  `RewriteRule` trait with `LEAN_THM` citation.

## `theory/` — Raw + Lens primitives

Mirrors `lean/E213/Theory/` and `lean/E213/Lens/`.

- `raw/internal.rs` — `pub(crate) Tree { A, B, Slash(...) }`.
  Invisible outside crate.
- `raw/mod.rs` — `pub struct Raw(Tree)` (newtype, private field).
  API: `a()`, `b()`, `slash(x, y, w)`, `fold`, `swap`, `depth`,
  `leaves`.  `slash` requires a `NotEq` witness.
- `lens.rs` — sealed `Lens<A>` with `lean_thm: &'static str`.
  `view = fold`, `equiv`, `refines`.  Constructor `__new__` is
  `pub(crate)` — only `lens/` factories can build new lenses.

## `lens/` — Lens instances + cohomology

Mirrors Lean's canonical lens definitions and `Math/Cohomology/`.

- `canonical.rs` — `lens_leaves`, `lens_depth` (mirror Lean defs).
- `chiral_k32.rs` — `lens_chiral_k32` for K_{3,2}^{(2)} graph.
  Cites `Linalg213.Capstone.paper1_chiral_compression`.
- `cohomology.rs` — δ², Hodge ⋆, flux operators expressed as
  Lens compositions.  Lazy: only ops used downstream materialize.

## `os/` — Atomicity + Analysis213 algorithms

Mirrors `lean/E213/OS/` and `lean/E213/Math/Analysis213/*`.

- `atomicity.rs` — `Atomic n`, `NonDecomposable`.
- `arity.rs` — `ArityForcing`, `Pigeonhole`, `PrimitiveSizes`.
- `canonical_part.rs` — (3, 2) split derivation.
- `analysis213/cut.rs` — `cutSum`, `cutMul`, `cutMid`,
  `cutBisection`, `cutPow`.  Each cites a Real213 lemma.
- `analysis213/dyadic.rs` — bracket, trajectory, Riemann.
- `analysis213/derivative.rs`, `integral.rs` — added on demand.

**Lazy rule:** add a function only when an `app/` calculation
requires it.  `whitelist.toml` is the gate.

## `app/` — concrete 213 calculations

Mirrors `lean/E213/App/Simplex.lean` and `lean/E213/Physics/`.

- `simplex.rs` — `Fin 5`, (3, 2) partition, `BlockPair` classifier.
- `basel.rs` — `S(N)`, `upper(N)` from `Physics.Basel`.
- `alpha_em.rs` — `inv_lower_tight`, `inv_upper`,
  `bracket_137_in_at_*` re-execution.
- `magic_numbers.rs` — 7/7 magic via 600-cell enumeration.
- Each function emits a certificate step.
