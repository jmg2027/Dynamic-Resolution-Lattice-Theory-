# rust-engine — DRLT 213 computation kernel in Rust

A layered Rust engine that computes inside the 213 world.  Not a fast
calculator that paraphrases Lean — a structural mirror of `lean/E213/`
where every runtime operation cites a 0-axiom Lean theorem.

**Status:** spec draft, no code yet.  See `docs/milestones.md`.

## Design constraints (non-negotiable)

1. **Zero-Fudge.** No external physics constants.  No `f32`/`f64` in
   any runtime crate.  ℕ + ℚ-as-(ℕ,ℕ) only.
2. **Lean is the ground truth.** Rust never claims theorems.  Each op
   declares `LEAN_THM: &'static str`; CI verifies the citation exists
   in `lean/E213/` and is closed at 0 axiom.
3. **Layered like Lean.** Crate dependency graph mirrors the Lean
   import graph: `kernel ← firmware ← hypervisor ← os ← app`.  Reverse
   imports are compile errors.
4. **No abstractions absent in 213.** No `Q.add`/`Q.mul` types.  No
   `impl Add for Q`.  Each Lean `def` becomes one Rust `fn` with the
   ℕ recursion inlined exactly as written in Lean.
5. **Certificate-only trust path.** Rust → ℚ-pair JSON certificate
   → Lean checker → 0-axiom verdict.  No FFI on the trust path.

## Layout (planned)

```
rust-engine/
├── crates/
│   ├── kernel/        # Term, Compare, Pair, Rat, NormalForm
│   ├── firmware/      # Raw (opaque), Lens (sealed)
│   ├── hypervisor/    # Lens instances; chiral K_{3,2}^{(2)}
│   ├── os/            # Atomicity, Pigeonhole, Analysis213 algos
│   └── app/           # Simplex, Basel, AlphaEM, magic numbers
├── docs/
│   ├── architecture.md
│   ├── layers.md
│   ├── trust-contract.md
│   └── milestones.md
├── whitelist.toml     # op ↔ Lean theorem ↔ Rust path triples
└── Cargo.toml         # workspace
```

## Documents

- `docs/architecture.md` — layered design, dep graph
- `docs/layers.md` — per-crate responsibilities
- `docs/trust-contract.md` — citation system, certificate format
- `docs/milestones.md` — phase plan (P0 — P5+)

## Authors

- Mingu Jeong (Independent Researcher) — theory, design.
- Claude (Anthropic) — formalization assistance, code drafting.
