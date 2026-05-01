# 213 Math Books — Index

Narrative volumes in 213-internal vocabulary.  Each book accompanies
a corresponding cluster of Lean files in `lean/E213/` and is closed
at ≤ {propext, Quot.sound} or STRICT 0-AXIOM.

## Volumes

| # | Title | Lines | Lean source |
|---|---|---|---|
| 1 | `analysis213.md` | 906 | `lean/E213/Research/Real213/*.lean` (180 files) |
| 2 | `number-theory-213.md` | 455 | `lean/E213/Math/Cohomology/Dyadic/**/*.lean` (~120 files) + `lean/E213/Meta/{BitPattern,UniversalLens*}.lean` |
| 3 | `cohomology-213.md` | 362 | `lean/E213/Math/Cohomology/` |
| 4 | `linalg-213.md` | 269 | `lean/E213/Math/Linalg213/` |
| 5 | `probability-213.md` | 328 | `lean/E213/Research/Real213/*` (probability surface) |
| 6 | `universal-lens-213.md` | 332 | `lean/E213/Meta/UniversalLens*.lean` + `Firmware/Raw.lean` (paper-style exposition) |

Total: ~2700 lines of narrative covering ~700 Lean files.

## Reading order

### Path A — Foundation first (recommended for new readers)

```
1. analysis213.md     calculus (familiar ground in 213 vocabulary)
2. linalg-213.md      Paper 1 Chiral Compression (rank ≤ 5)
3. cohomology-213.md  K_{3,2}^{(c=2)} structure
4. number-theory-213.md  Pisano, Legendre, Universal Lens
```

### Path B — Highlights first (for impatient readers)

```
1. number-theory-213.md  Universal Lens metatheory (Open Problem #6)
2. cohomology-213.md     Δ⁴ Leibniz + α_GUT cohomologically
3. linalg-213.md         rank-5 compression
4. analysis213.md        constructive calculus context
```

### Path C — Topic-first

- **Universal Lens / metatheory** → `number-theory-213.md` Part IV
- **Pisano CRT / Legendre lens** → `number-theory-213.md` Parts II-III
- **Cohomology / Δ⁴ Leibniz** → `cohomology-213.md` Parts II-III
- **Hodge involution** → `cohomology-213.md` Part IV
- **Fractal α_GUT decomposition** → `cohomology-213.md` Part VI
- **Paper 1 Chiral Compression** → `linalg-213.md` Parts II-IV
- **Constructive analysis** → `analysis213.md`

## Vocabulary cheat sheet

| Term | Meaning |
|---|---|
| Raw | Free commutative magma on {a, b} via slash with x ≠ y |
| Lens α | (base_a, base_b, combine) packaged with view : Raw → α |
| Atomicity | d = 5 unique by Bézout shift; (NS, NT) = (3, 2) by PairForcing |
| K_{3,2}^{(c=2)} | Canonical chiral bipartite multigraph |
| ArithFSM_d | d-state arithmetic FSM (multiplicative / Pell / Tribonacci) |
| BitFSM | Generic finite-state Bool stream generator |
| Q213 | Term × Term — 213-native rational pair |
| signature | K_{3,2}^{(c=2)} trajectory in Fin 5 |
| Cup / AW / CupAW | Alexander-Whitney cup product on cochains |
| δ | Coboundary operator; δ² = 0 |
| Hodge ⋆ | Dual cochain via canonical pairing on K5 |
| Bipartite32 | Concrete K_{3,2}^{(c=2)} cochain machinery |

## Companion materials

- **Lean source**: `lean/E213/` — all theorems referenced verifiable
  via `lake build E213` + `#print axioms`.
- **Rust verification engine**: `rust-engine/` — independent ℕ-only
  verification; cross-checks Lean theorems via citation manifest.
- **Blueprints**: `blueprints/math/` — planning roadmaps for
  remaining fields (probability, multivariable, topology, ...).
- **Focused papers**: `books/math/papers/` — academic-paper-style
  expositions of standalone results.
- **Catalogs**: `catalogs/` — atomic-integer reference + falsifier
  ledger.

## Realisation status

See `blueprints/math/INDEX.md` for the full realisation snapshot.
Summary:

- ✅ **Number Theory 213** — `number-theory-213.md`
- ✅ **213 Meta** (Universal Lens) — `number-theory-213.md` Part IV
- ✅ **Cohomology 213** — `cohomology-213.md`
- ✅ **Calculus** — `analysis213.md`
- 🟡 **Linear Algebra 213** (Paper 1) — `linalg-213.md`
- 🟡 **Combinatorics 213** — partial (atomicity + Pell families)
- ⏳ Probability, Multivariable, Topology, Complex, Measure, ODE,
  Functional, Group, Information, Logic — pending future marathons.

## Verification standard

Every theorem referenced in these books is closed in Lean 4 at:

  ≤ {propext, Quot.sound}    (Lean 4 kernel floor), OR
  STRICT 0-AXIOM             (concrete computations, encodings)

No `sorry`, no Mathlib, no Classical, no native_decide.

## Author

Mingu Jeong (Independent Researcher).

Acknowledgments: Claude (Anthropic) provided formalization
assistance under direct supervision.
