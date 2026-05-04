# rust-engine — DRLT 213 computation kernel

A layered Rust engine that computes inside the 213 world.  Not a fast
calculator that paraphrases Lean — a structural mirror of `lean/E213/`
where every runtime operation cites a 0-axiom Lean theorem.

## Status

- **53 binaries** (`crates/app/src/bin/*.rs`)
- **184/184 tests** pass (`cargo test --release --workspace`)
- **94/94 citations** resolve at theorem-id level
  (`tools/verify-citations`)
- **0 external transcendental inputs** in runtime crates
  (π via Leibniz `wallis::pi_bracket`, ζ(2) via Basel
  `s_partial`/`upper`)

## Headline precision results (★★ sub-ppm)

| observable | DRLT | observed | Δ | binary |
|---|---|---|---|---|
| HO magic 2,8,20 | exact | exact | 0 | `magic-numbers` |
| N_gen = 3 | exact | 3 | 0 | `generations` |
| Muon prefactor 192 | exact | 192 | 0 | `muon-lifetime` |
| m_μ/m_e | 206.7682837 | 206.7682838 | 0.49 ppb | `mu-electron` |
| m_p | 938.271472 MeV | 938.2700 MeV | 1.56 ppm | `m-proton` |
| 1/α_em | 137.0359895 | 137.0359991 | 0.07 ppm | `alpha-em-bracket` |
| m_b/m_c | 3.291805 | 3.291338 | 142 ppm | `mb-mc-sweep` |
| Top y_t | 0.991894 | 0.991879 | 15 ppm | `top-yukawa` |
| 1/α_3 v2 | 8.475971 | 8.476 | 0.0003% | `triple-coupling` |
| Ω_Λ | 0.685 ∈ [0.6845, 0.6855] | 0.685 | bracket OK | `dark-energy` |

Full table: `docs/precision-matrix.md`.

## Cohomology classification (A/B/C/D/E)

Every observable in DRLT decomposes into one of five operational
classes on K_{3,2}^{(c=2)} cochains:

- **A** — single-simplex propagator P(x) = (1+2x)/(1+x).
  α_em Dyson tail, m_μ/m_e, m_p, λ_H V(x).
- **B** — boundary-leakage linear (1 + α_GUT·k).
  m_b/m_c (k=NT²), Top Yukawa (k=−1/NS).
- **C** — full-lattice bare invariant (Betti / atomic integer).
  1/α_3 = NS²−1 = 8, sin²θ_ij, m_t/m_c skeleton.
- **D** — chain product (cup ⌣ in cochain ring).
  m_t/m_c via C × B chain, neutrino m_3/m_2.
- **E** — modulus shadow |G_ij|²/d (gravity readout of same Gram).
  Ω_Λ, M_Pl/v_H, Λ_QCD-as-unit-anchor.

100% hit rate on a 36-observable corpus
(`scale-ladder-classify` binary).  The class is forced by
algebraic form alone — predictor algorithm in
`docs/cohomology-classes.md`.

## Document map

- `docs/precision-matrix.md` — full results table.
- `docs/cohomology-classes.md` — A/B/C/D/E framework, predictor
  algorithm, fractal scale ladder b_1(L) = (5^L−1)(5^L−2)/2.
- `docs/gaps-and-todos.md` — engineering audit, all entries
  closed (✅ §1-§6) or honestly flagged (🟡 §7c m_t/m_c).
- `docs/closure-algorithm.md` — DRLT Closure Form pattern (Hunter
  methodology, cited from CLAUDE.md as the L1–L5 closure lessons).
- `docs/math-branch-physics-notes.md` — ~3000-line accumulator of
  physics-applicable intuition mined from the (now-integrated)
  math-track branch.  ~250 Lean files cross-walked across three
  sections (Cohomology + Linalg + Math/, Dyadic Number Theory,
  Real213 constructive analysis).
- `docs/architecture.md`, `layers.md`, `trust-contract.md`,
  `milestones.md` — design references.

## Design constraints (non-negotiable)

1. **Zero-Fudge.** No external physics constants.  No `f32`/`f64`
   in any runtime crate.  ℕ + ℚ-as-(ℕ,ℕ) only.  π via Leibniz
   bracket, ζ(2) via Basel — no transcendental hardcodes.
2. **Lean is the ground truth.** Rust never claims theorems.
   Each binary cites a Lean theorem in `whitelist.toml`;
   `tools/verify-citations` checks file resolution + identifier
   match at depth ≥ 2.
3. **Layered like Lean.** Crate dependency graph mirrors the Lean
   import graph: `kernel ← firmware ← hypervisor ← os ← app`.
4. **Certificate-only trust path.** Rust → ℚ-pair → Lean checker
   → 0-axiom verdict.  No FFI on the trust path.

## Layout

```
rust-engine/
├── crates/
│   ├── kernel/        # Term, Compare, Pair, Rat, NormalForm
│   ├── firmware/      # Raw (opaque), Lens (sealed)
│   ├── hypervisor/    # Lens instances; chiral K_{3,2}^{(2)}
│   ├── os/            # Atomicity, Pigeonhole, canonical_part
│   └── app/           # Simplex, Basel, AlphaEM, wallis,
│                      # 53 binaries
├── docs/              # see "Document map" above
├── tools/
│   └── verify-citations/   # whitelist ↔ Lean theorem checker
├── whitelist.toml     # 94 (rust path → Lean theorem) rows
└── Cargo.toml         # workspace
```

## Build & verify

```
cd rust-engine
cargo build --release --bins        # all 53 binaries
cargo test  --release --workspace   # 184 tests
DRLT_REPO_ROOT=$(cd .. && pwd) ./target/release/verify-citations
                                    # 94/94 OK
```

Each binary takes optional precision args, e.g.
`mu-electron 5000` or `dark-energy 5000 200` (N_ζ N_π).

## Authors

- Mingu Jeong (Independent Researcher) — theory.
- Claude (Anthropic) — formalization assistance, code drafting.
