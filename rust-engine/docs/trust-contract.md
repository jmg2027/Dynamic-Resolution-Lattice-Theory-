# Trust contract — Lean ↔ Rust

## Direction

```
Rust  ──(certificate)──→  Lean checker  ──→  0-axiom verdict
```

Single direction.  Lean kernel never depends on Rust output.  No FFI
on the trust path.  Rust may invoke `lake env lean` from a build
script for tests, never linked into runtime.

## Citation system

Every Rust function in `os/`, `hypervisor/`, `app/` that computes
a 213 quantity declares:

```rust
pub const LEAN_THM: &'static str = "E213.Lib.Physics.Basel.S_3";
```

`whitelist.toml` is the single source of truth:

```toml
[[op]]
rust = "app::basel::S"
lean = "E213.Lib.Physics.Basel.S"
test = "S(3) == (49, 36)"
```

`verify-citations` (build-time binary) checks:

1. The Lean theorem exists in `lean/E213/`.
2. `lake build` succeeds.
3. `#print axioms <thm>` returns "does not depend on any axioms"
   (empty list / PURE) — a `propext`/`Quot.sound`/Classical citation
   is DIRTY and breaks the build (per `STRICT_ZERO_AXIOM.md`).
4. Every public function in runtime crates is in `whitelist.toml`.

Missing or non-zero-axiom citation breaks the build.

## Certificate format

```
Certificate = [Step]

Step =
  | Const  { name: String, value: (Nat, Nat) }
  | Apply  { op: OpName, args: [(Nat, Nat)], result: (Nat, Nat) }
  | Bound  { lhs: (Nat, Nat), cmp: "<"|"≤"|"=", rhs: (Nat, Nat) }
  | Cite   { lemma: LeanThmName }
```

All numbers ℕ.  Lean checker reads JSON, re-runs each `Apply` via
the cited lemma's `#eval`, verifies `Bound` by `decide`.

## Forbidden in runtime crates

- `f32`, `f64`, `std::f64::*` (CI lint).
- `unsafe`.
- External numeric crates ≠ `num-bigint`, `num-rational`.
- Observed-value constants (e.g. `1.0/137.0359...`).
- `impl Add for Q` or any Q-algebra typeclass.
- `extern "C"` calling Lean from runtime path.

## Allowed in dev zone

`dev-tools/`, `examples/`, `benches/`, `build.rs` may use floats
and any crate, **only** if not in any runtime `[dependencies]`.

## CI gates (per-commit)

1. `lake build` clean, 0-axiom audit.
2. `cargo build --workspace --release` clean.
3. `cargo run --bin verify-citations` pass.
4. `cargo test --workspace` (property tests vs Lean `#eval`).
5. `cargo clippy -- -D clippy::float_arithmetic`.
6. Reverse-import grep: lower crates cannot mention upper.
