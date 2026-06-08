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

## Honest status

- **Demoted**: `δ = π/φ²` (Niven-forbidden golden phase; was a posit `176/147`,
  and a mediocre `68.75°` vs `γ_obs=65.1°`).
- **`α = 90°` is still an input** — motivated by the CD `i` / right-triangle /
  maximal-CP program (and `α_obs≈92°`), but not rigorously forced to be the CKM
  `α`.  The fit is decent (`β` exact, `α,γ` ~1.5σ), not perfect.
- **The advance is principled-ness**, not precision: the phase is now a Niven-
  allowed root of unity consistent with every no-go, and `cos γ = 1/φ²` is a
  clean golden *output*.

## What "new territory" would close it fully

To *derive* (not posit) `α=90°`: a forcing theorem that the single KM phase is
pinned to the CD `i` (the `C₄` unit) — i.e. that the 3-generation flavour space
is wired to the `NT=2` CD doubling such that the surviving rephasing-invariant
phase is exactly `arg i = π/2`.  This is the precise missing bridge: a
**complex-type (`FS=−1`) representation of the 3 generations carrying the CD `i`**,
evading the A₅ reality wall.  The CD tower has the `i` (`ℤ[i]`, `C₄`) and 213 has
`N_gen=3`; what is unbuilt is the wiring between them.

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
