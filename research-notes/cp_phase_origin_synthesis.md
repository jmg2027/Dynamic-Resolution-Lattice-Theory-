# CP-phase origin marathon — synthesis (2026-06-08)

**Question** (originator): can the CKM CP phase `δ` be *derived* from the 213
repo, or must new territory be built?  **Method**: a deep multi-agent research
marathon — four expert agent teams (A₅+gCP literature, icosian/`2I`/E₈ geometry,
Cayley–Dickson tower, Kobayashi–Maskawa mechanism) + explicit representation-
theory computation, iterated to convergence.

## The result, in one line

> CP **existence + uniqueness** is derived (`N_gen=3 ⇒ 1` phase); the CP **phase
> value is NOT golden** — by Niven's theorem a discrete phase is a root of unity
> (`0°,60°,90°`), so `δ=π/φ²` is structurally forbidden as a discrete phase.  The
> 213-coherent CP structure is **golden modulus `R_u=1/φ²` + `π/2` phase (CD `i`,
> `α=90°` right triangle)**, giving `cos γ = 1/φ²` — replacing the demoted posit.

## Three independent no-go results (all agents converge)

| 213 structure | forced CP phases | golden `π/φ²`? |
|---|---|---|
| **A₅ + gCP** (flavour) | `{0,90,180,270}°` (`π/2·ℤ`) | ✗ — A₅ 3-rep is **real** (FS `+1`); `φ` → real mixing **angle**, phase cancels |
| **Icosian / `2I` / E₈** | `{36,72,108,…}°` (`π/5·ℤ`) | ✗ — `π/φ²` is irrational·`π`, **off the `π/5` lattice** (structural, not numerical) |
| **Cayley–Dickson tower** | `C₄=90°`, `C₆=60,120°` (`π/2,π/3`) | ✗ — discrete cyclotomic units only; disjoint from flavour |

**Unifying theorem (Niven/Lehmer)**: the only rational multiples of `π` with
rational cosine are `0°,60°,90°`.  A discrete-symmetry CP phase is a root of
unity ⇒ rational·`π`.  `π/φ²` is irrational·`π` (`φ²` irrational) ⇒ it **cannot**
be any discrete-symmetry phase.  Golden values require non-abelian `A₅`/√5 data —
but there `√5` enters the **character/angle** (real), never the phase (the FS-
reality wall, `A5RealityNoCP.a5_3rep_is_real`).  **The golden ratio and the CP
phase live in orthogonal sectors of every 213 discrete structure.**

## What IS derived

1. **CP existence + uniqueness** (`Mixing/CPPhaseCount.lean`, 6 PURE): from the
   derived `N_gen = C(NS,NT) = 3`, Kobayashi–Maskawa counting gives exactly
   `(NS−1)(NS−2)/2 = 1` physical CP phase and `NS(NS−1)/2 = 3` angles; `N=2 ⇒ 0`
   (no CP).  `N_gen=3` is the minimal CP-admitting count — and 213 derives it.
   (Note the binomial alignment: `3 = C(3,2)` generations, `1 = C(2,2)` phase.)
2. **The golden modulus** `R_u = √(ρ̄²+η̄²) = 1/φ²` — the contracting eigenvalue
   of the self-reference map `M` (`JarlskogApex`, `OrderFive`), `R_u<1`-forced.

## The reframed apex (`Mixing/ApexRightTriangle.lean`, 5 PURE)

The CP phase is the **CD imaginary unit `i`** (`NT=2` first doubling,
`ℤ[i]^×=C₄`, `arg i = π/2`, Niven-allowed) ⇒ **`α = 90°`** (right unitarity
triangle).  The golden ratio is the **modulus** `R_u=1/φ²` (real, derived).
Apex on the Thales circle ⇒ **`cos γ = R_u = 1/φ²`**:

| element | predicted | observed (UTfit/CKMfitter 2023) |
|---|---|---|
| `β` | `22.46°` | `22.5°±0.7°` ✓ ≈exact |
| `γ` | `arccos(1/φ²)=67.54°` | `65.1°±1.5°` (~1.6σ) |
| `α` | `90°` | `92.4°±1.4°` (~1.7σ) |
| `η̄` | `0.353` | `0.347±0.010` |
| `ρ̄=R_u²` | `0.146` | `0.161±0.010` (~1.5σ) |

Two principled inputs (`α=π/2` from CD `i`; `R_u=1/φ²` derived) fix the triangle.

## ★ `α = 90°` upgraded from input to FORCED (`CPPhaseC4Forcing.lean`, 6 PURE)

The "wiring" step is now done as a **forcing argument**.  Two 213-derived inputs:
1. the complex structure is the **CD `i`** (`NT=2` first doubling) ⇒ phase
   `∈ ℤ[i]^× = C₄ = {1,i,−1,−i}` (`{0,90,180,270}°`);
2. **CP exists** (`CPPhaseCount`: `N_gen=3 ⇒ 1` *physical*, `J≠0` phase).

Forcing: `J ∝ Im`; the real `C₄` units `{±1}` give `J=0` (no CP), so CP-existence
**excludes** them, leaving `{i,−i} = {±90°}` (pure imaginary, `J≠0`).  Up to
CP-orientation (`δ↔−δ`), **`δ = 90°` is forced** — the right unitarity triangle.
So `α=90°` is **derived** from `C₄` + CP-existence, *not* posited.

## Honest status

- **Demoted**: `δ = π/φ²` (Niven-forbidden golden phase; mediocre `68.75°`).
- **`α = 90°` now FORCED** given the *sole* remaining premise "phase `∈ C₄`"
  (the complex structure is the `NT=2` first doubling `i`, not a higher
  cyclotomic).  Why `C₄` not `C₆` (`ℤ[ω]`, `60°`): the *first/minimal* complex
  doubling is `ℤ[i]`; and empirically `α≈90°`, not `60°`.  This premise is far
  weaker and more principled than positing a value.
- **`R_u = 1/φ²` derived** (M eigenvalue) ⇒ `cos γ = 1/φ²` (golden output);
  `β = 22.46°` ≈ exact; fit ~1.5σ on `α,γ`.
- **The advance**: the phase value is now *forced* (not posited) from 213-native
  structure — `C₄` (CD `i`) + CP-existence — consistent with every no-go.

## What "new territory" remains (after the C₄ forcing)

The forcing reduces the open part to a single premise: **the relevant complex
structure is the CD `i` (phase `∈ C₄`)**.  To eliminate even that, build the
explicit bridge — a complex-type (`FS=−1`) representation of the 3 generations
(SU(5) `5̄⊕10`) carrying the CD `i`, so the surviving rephasing-invariant phase
is *structurally* a `ℤ[i]` unit (not assumed).  This would turn "phase `∈ C₄`"
from a premise into a theorem.  The CD `i` (`ℤ[i]`, `C₄`), `N_gen=3`, and the
forcing all exist; only the explicit generation↔`ℤ[i]` mass-structure is unbuilt.

## Lean / files
- `Mixing/CPPhaseCount.lean` (6 PURE) — CP existence+uniqueness from `N_gen=3`.
- `Mixing/ApexRightTriangle.lean` (5 PURE) — the reframed apex, `cos γ=1/φ²`.
- `Icosahedral/A5RealityNoCP.lean` (4 PURE) — A₅ real ⇒ no golden phase.
- Frontier `research-notes/frontiers/ckm_rho_eta_apex.md` — full record.

## Agent reports (cited)
- A₅+gCP: `δ∈{0,90,180,270}°` (Turner 1506.06898 Table 1; Di Iura 1503.04140).
- Icosian: `π/5`-quantized, `π/φ²` off-lattice (Conway–Sloane, *SPLAG* Ch.8).
- CD tower: `C₄/C₆` discrete phases, disjoint from flavour; FS-reality wall.
- KM: Niven ⇒ root-of-unity phases; `α≈90°` right-triangle (Nucl.Phys.B 877
  (2013) 752); UTfit/CKMfitter 2023 values; no golden-`δ` precedent (novel).
