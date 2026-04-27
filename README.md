# 213 Library

> Derive all of mathematics and physics from *primitive distinction* — Lean 4 core only, Mathlib-free.

## What It Is

**213** = Starting from the *minimal residue* with 4-clause raw axiom.

```
DRLT (Dynamic Resolution Lattice Theory)
  = Raw axiom (a, b, /, distinctness)
  + Lens framework
  → Atomicity (NS=3, NT=2, d=5)
  → Derive all of Math + Physics
```

## Core Stakes

- **0 sorry, 0 external axiom** (Lean 4 core only)
- ≤ propext + Quot.sound (most at 0 axioms)
- ★ **213 Kernel: 101 theorems *literally 0 axiom*** (deep embedding,
  neither propext/Quot.sound is load-bearing)
  → Formal proof of "Lean = syntactic host, 213 = real foundation"
  → Verify: `./tools/kernel_regress.sh`
- *No numerical analysis* — rational arithmetic + decide
- *Mathlib-free*
- *Measurement falsifiers* 14+ (1 observation violation → discard, 8 of these axiom-free)

## Directory

```
seed/            seeds (axioms + philosophy + falsifiability)
lean/E213/       Lean 4 formal library (634 files)
  ├── Kernel/    ★ deep-embedded 213 kernel (14 files, 101 theorems 0 axiom)
  ├── Physics/   physics formalization (227 files)
  ├── Research/  research / exploratory (331 files)
  ├── Math/      mathematics (8 files)
  ├── Firmware/  low-level layer: Raw axioms, RawLevels, RawSwap (13 files)
  ├── OS/        atomicity + canonical structures (8 files)
  ├── App/       applications: simplex geometry (1 file)
  ├── Hypervisor/ cross-layer bridge (1 file)
  ├── Infinity/  limit / compactification layer (9 files)
  ├── Meta/      meta-theory utilities (9 files)
  └── Tactic/    custom tactics (10 files)
blueprints/      meta/2 + math/14 + physics/14
books/           narrative hierarchy (math/, physics/)
papers/          16 journal .tex papers + drlt-book/
catalogs/        lookup tables (atomic integers, constants, periodic table, falsifiers)
tools/           automation (audit, port_candidates, auto_port, regress, FORBIDDEN)
research-notes/  research notes
```

## Usage

```lean
import E213.Physics.Phase4.Library

open E213.Physics.Phase4.Library.IELibrary

#check IE_H_micro       -- 13598434 μeV (4.3 ppb formal)
```

## Build

```bash
cd lean/
lake build E213
```

## Key Results

### Physics
- 1/α_em = 137.036 (ppm, 5-term simplicial sum)
- m_p = 938.27 MeV (0.000% lattice precision)
- m_μ/m_e = 206.768 (0.48 ppb)
- Ω_Λ = 0.685 (0.0008%)
- Magic numbers 7/7 exact
- Periodic table 113 + 5 super-heavy atomic

### Math
- Undergraduate calculus 100% (Real213 Phase J→DK)
- 213-native derivative = cohomological flux
- exp(0), sin(0), cos(0) atomic

## Authors

- Mingu Jeong (Independent Researcher)
- Claude (Anthropic): formalization, Acknowledgments
- 0 sorry, 0 external axioms

## License

This is a **research repository, not an open-source library**.
Check the license before use.

| Scope | License | Meaning |
|---|---|---|
| `lean/`, `tools/`, `.claude/` (code) | **PolyForm Noncommercial 1.0.0** | Free academic/non-commercial use & modification; commercial use *prohibited* |
| `book/`, `papers/`, `blueprints/`, `seed/`, `catalogs/`, `books/`, `research-notes/` (prose) | **CC BY-NC-ND 4.0** | Attribution + non-commercial + *no derivatives* |

Details: [`LICENSE`](LICENSE) (code) · [`LICENSE-DOCS`](LICENSE-DOCS) (prose)

Academic citation, research reproduction, and educational use are welcome.
Commercial fork / productization / unauthorized translation / unauthorized modification is prohibited.

Copyright © 2026 Mingu Jeong.
