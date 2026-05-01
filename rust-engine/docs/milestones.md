# Milestones

Each phase ends with green CI: `lake build` + `cargo build` +
`verify-citations` + property tests pass on the new surface.

## Phase 0 — Skeleton

Goal: workspace compiles, citation infrastructure runs.

- `Cargo.toml` workspace with 5 empty crates.
- `kernel/term.rs` — `Term` ↔ `BigUint` round trip.
- `kernel/compare.rs` — `le_b`, `equiv` (Bool).
- `kernel/rat.rs` — `(BigUint, BigUint)` + `equivQ` + `leQ`.
- `firmware/raw/internal.rs` — `pub(crate) Tree`.
- `firmware/raw/mod.rs` — `Raw` opaque + `a`/`b`/`fold`/`swap`/
  `depth`/`leaves`/`slash`+`NotEq` witness.
- `firmware/lens.rs` — sealed `Lens<A>` + `view`/`equiv`/`refines`.
- `whitelist.toml` v0.1 (~10 entries).
- `tools/verify-citations/` binary + CI workflow.

Exit: `cargo build` green, 10 whitelist entries audit clean.

## Phase 1 — First lens (paper 1 capstone)

Goal: K_{3,2}^{(2)} chiral lens reproduces
`paper1_chiral_compression`.

- `hypervisor/canonical.rs` — `lens_leaves`, `lens_depth`.
- `hypervisor/chiral_k32.rs` — `lens_chiral_k32`.
- Property test: random `Raw` of depth ≤ 6, Lean `#eval` ≡ Rust.

Exit: paper 1 capstone re-executable + certificate.

## Phase 2 — Normal form

Goal: decidability bridge for algebraic identities.

- `kernel/normal_form.rs` — `Monomial { p, q }`, `RewriteRule` trait.
- 5 starter rewrite rules, each citing a Lean lemma.
- Round-trip: `normalize(e)` ≡ Lean `decide` verdict.

Exit: monomial canonical form available to higher crates.

## Phase 3 — OS foundations

Goal: Atomicity + (3, 2) split available.

- `os/atomicity.rs`, `os/arity.rs`, `os/canonical_part.rs`.
- 8 whitelist entries (one per Lean OS file).

Exit: `app/simplex.rs` can ground itself in OS layer.

## Phase 4 — α_em bracket re-execution

Goal: first end-to-end physics number with certificate.

- `app/simplex.rs` — Fin 5, (3, 2), BlockPair classifier.
- `app/basel.rs` — `S(N)`, `upper(N)` matching `Basel.S_0..3`.
- `app/alpha_em.rs` — `inv_lower_tight`, `inv_upper`,
  `bracket_137_in_at_20`.
- Certificate emitter (JSON) + `lean/E213/Tools/CertChecker.lean`.
- End-to-end: Rust runs → certificate → Lean accepts (0-axiom).

Exit: `cargo run --bin alpha-em-bracket -- --N 20` verifiable.

## Phase 5+ — Lazy expansion

Each new observable: Lean lemma (if missing) + Rust mirror +
whitelist entry + property test + certificate step.

Candidates: m_p, m_μ/m_e, magic numbers, η_B, Ω_Λ.  Order TBD.

## Out of scope (now)

- Linalg213 / Cohomology213 full mirror — only ops on α_em path.
- Real213 cut algebra — only `S` + `upper` until needed.
- Concurrency (rayon).  Single-threaded until benches demand.
