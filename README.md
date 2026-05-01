# 213 Library

> Derive all of mathematics and physics from *primitive distinction* —
> Lean 4 core only, Mathlib-free, ℕ-only Rust verification engine.

## What It Is

**213** = Starting from the *minimal residue* with a 3-clause Raw axiom
(plus directionless slash_comm).

```
DRLT (Dynamic Resolution Lattice Theory)
  = Raw axiom (a, b, slash, slash_comm)
  + Lens framework
  → Atomicity (d = 5 unique, NS = 3, NT = 2 forced)
  → K_{3,2}^{(c=2)} graph (canonical)
  → Mathematics + Physics derived
```

## Core stakes

- **0 sorry, 0 Mathlib, 0 Classical, 0 native_decide**
- ≤ {propext, Quot.sound} (Lean 4 kernel floor; many results STRICT 0-AXIOM)
- ★ **Kernel layer 0-axiom**: deep-embedded `Term` system; neither
  propext nor Quot.sound is load-bearing for the kernel itself.
  Verify: `./tools/kernel_regress.sh`
- *No numerical analysis* — ℕ + ℚ-as-(ℕ, ℕ) only.  π via Wallis brackets,
  ζ(2) via Basel — no transcendental hardcodes.
- *Mathlib-free* throughout.
- *Independent Rust verification engine* — 53 binaries, 184 tests,
  94 Lean-theorem citations resolved at theorem-id level.

## Headline results (sub-ppm physics)

| Observable | DRLT | Observed | Δ |
|---|---|---|---|
| 1/α_em | 137.0359895 | 137.0359991 | **0.07 ppm** |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.49 ppb** |
| m_p | 938.271472 MeV | 938.2700 MeV | **1.56 ppm** |
| H ionization | 13.605693 eV | 13.605693 eV | **4.3 ppb** |
| Magic numbers 2,8,20 | exact | exact | EXACT |
| Muon prefactor 192 | exact | 192 | EXACT |

## Famous coincidences elevated to derivations

| Coincidence | Year | DRLT form |
|---|---|---|
| 1/α_em ≈ 137 (Eddington) | 1929 | 60·ζ(2) + 30 + 25/3 + α_GUT corr. |
| m_p/m_e ≈ 6π⁵ (Lenz) | 1951 | NS · NT · π⁵ |
| Koide 2/3 | 1981 | NT / NS |
| Hierarchy M_Pl/v_H | 1980s | d^(d²) / (d+1) = 5^25/6 |

## Universal Lens metatheory

```
expSumLens : Lens (ℕ × ℕ)        Function.Injective expSumLens.view
q213Lens   : Lens (Q213 × Q213)  Function.Injective q213Lens.view
                                  (Q213 := Term × Term, 213-native ℚ)
```

Both at ≤ {propext, Quot.sound}.  Every Raw element is uniquely
encoded as a pair of 213-native rationals via a symmetric commutative
magma operation — the formal expression of the G1 thesis
("213 is the precondition for any describing").

## Directory

```
seed/            axioms + philosophy + falsifiability
lean/E213/       Lean 4 formal library (~800 files)
  ├── Kernel/    ★ deep-embedded 213 (Term, Compare, Pair, Rat,
  │              NormalForm)
  ├── Firmware/  Raw (canonical-form), Lens
  ├── Hypervisor/ Lens instances; chiral K_{3,2}^{(c=2)}
  ├── OS/        Atomicity, PairForcing, Pigeonhole
  ├── App/       Simplex, BaselBound, AlphaGUT, AlphaEM, ...
  ├── Math/      Cohomology (147 files), Linalg213, Analysis
  ├── Physics/   86 files; couplings, masses, mixing, atoms,
  │              hadrons, nuclei, cosmology
  ├── Research/  research / exploratory (~300 files)
  ├── Meta/      Universal Lens metatheory + variants
  ├── Infinity/  limit / compactification
  └── Tactic/    custom tactics
rust-engine/     Independent ℕ-only verification (53 binaries,
                 184 tests, 94 citations)
blueprints/      math/14 + physics/14 + meta/2 (status snapshots)
books/           narrative hierarchy
  └── math/      analysis213 + number-theory-213 + cohomology-213
                 + linalg-213
  └── physics/   periodic-table + (more in rust-engine docs)
papers/          archived journal-style .tex papers
catalogs/        lookup tables (atomic integers, constants,
                 periodic table, falsifiers)
tools/           automation (audit, regress, FORBIDDEN)
research-notes/  research notes
```

## Build

```bash
cd lean/
lake build E213
# → ≤ {propext, Quot.sound}, no Mathlib, no Classical, no sorry
```

## Math books

```
books/math/
├── analysis213.md        Undergraduate year-1 calculus (100%)
├── number-theory-213.md  Pell, Pisano CRT, Legendre lens,
│                          Universal Lens metatheory
├── cohomology-213.md     K_{3,2}^{(c=2)}, Δ⁴ Leibniz,
│                          Hodge ⋆⋆, fractal α_GUT
└── linalg-213.md         Paper 1 Chiral Compression (rank ≤ 5)
```

See `books/math/INDEX.md` for reading order.

## Authors

- Mingu Jeong (Independent Researcher)
- Claude (Anthropic): formalization, Acknowledgments
- 0 sorry, 0 external axioms

## License

This is a **research repository, not an open-source library**.
Check the license before use.

| Scope | License | Meaning |
|---|---|---|
| `lean/`, `tools/`, `.claude/`, `rust-engine/` (code) | **PolyForm Noncommercial 1.0.0** | Free academic/non-commercial use & modification; commercial use *prohibited* |
| `books/`, `papers/`, `blueprints/`, `seed/`, `catalogs/`, `research-notes/` (prose) | **CC BY-NC-ND 4.0** | Attribution + non-commercial + *no derivatives* |

Details: [`LICENSE`](LICENSE) (code) · [`LICENSE-DOCS`](LICENSE-DOCS) (prose)

Academic citation, research reproduction, and educational use are welcome.
Commercial fork / productization / unauthorized translation / unauthorized modification is prohibited.

Copyright © 2026 Mingu Jeong.
