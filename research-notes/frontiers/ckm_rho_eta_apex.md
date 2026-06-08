# Frontier — the CKM Wolfenstein apex `(ρ, η)` and the Jarlskog magnitude

**Status**: OPEN. **Domain**: physics (CKM / CP violation).
**Opened**: 2026-06-07 (found auditing whether θ_QCD's `J` is derivable).

## The gap

The Jarlskog invariant's *structure* is DRLT-derived — all factors are
atomic:
- `s₁₂ = λ = 5/22 = d/(d²−d+c)` (Cabibbo, `CabibboAngle`/`CKMHierarchy`)
- `A = φ/c = φ/2` (golden-ratio-over-c, `CKMHierarchy`)
- `s₂₃ = A·λ²`, `s₁₃ = A·λ³`
- `δ = π/φ²` (`CPViolation`, `δ ≈ 68.75°`, `sin δ ≈ 0.932`)

But the *magnitude* does **not** match. Computed honestly from the full
formula `J = c₁₂s₁₂c₂₃s₂₃c₁₃²s₁₃ sin δ`:

  **J_DRLT = 8.18 × 10⁻⁵   vs   J_observed = 3.08 × 10⁻⁵   (×2.66 over)**

(A prior `CPViolation.lean` comment claimed "≈3.5×10⁻⁵, within 10%" — an
arithmetic error; its own factors multiply to 7.6×10⁻⁵. Corrected.)

## Root cause — the un-derived apex `(ρ, η)`

The discrepancy is localized to `s₁₃` / `|V_ub|`:
- observed `|V_ub| = A·λ³·√(ρ²+η²) ≈ A·λ³·0.39 ≈ 0.0037`
- DRLT uses `s₁₃ = A·λ³ = 0.0095` — **omitting `√(ρ²+η²) ≈ 0.39`**.

Equivalently `J = A²·λ⁶·η`, and DRLT has not derived the CP-apex
parameters `(ρ, η)` (only `λ`, `A`, `δ`). `s₂₃ ≈ A·λ² ≈ 0.042` matches
observed `|V_cb| ≈ 0.041` fine — the gap is specifically the apex.

## Consequences (tracked elsewhere)

- **θ_QCD (`PRE_REGISTRATION.md` P2)**: `θ_QCD = J·α_GUT⁴` inherits the
  un-derived `J`; with the honest `J = 8.18×10⁻⁵`, the θ_QCD central value
  shifts ×2.66, moving it outside the catalog's own `[2.51,3.00]×10⁻¹¹`
  bracket. P2 therefore depends on a `J` DRLT does not yet produce.
- **`DEGREES_OF_FREEDOM_LEDGER.md`**: the Jarlskog row is upgraded from
  "magnitude un-derived" to "magnitude over-predicted ×2.66; missing
  `(ρ, η)`".

## Candidate — the apex is a φ² object: modulus `1/φ²`, phase `π/φ²` (2026-06-07)

`JarlskogApex.lean` (PURE). Trying to force the first `c/d` guess revealed a
better, **φ²-coherent** candidate: the CKM CP-apex is a single golden object —
**modulus `R_u = 1/φ²`, phase `δ = π/φ²`** (the phase already derived in
`CPViolation`). The same `φ²` in both, and `φ²` is atomic
(`φ²+1/φ² = NS`, `d·NT = NS²+1`).

Numerical match (full Jarlskog formula, `R_u = 1/φ²`):
- `R_u = 1/φ² = 0.38197` vs observed `√(ρ̄²+η̄²) = 0.38260` (**0.17%**)
- `J = 3.12×10⁻⁵` vs observed `3.08×10⁻⁵` (**+1.4%**, was 166% without)
- `η = (1/φ²)·sin(π/φ²) = 0.356` vs observed `η̄ = 0.348` (**2.3%**)

The earlier `c/d = 2/5` is **not a competitor**: it is the *lowest Fibonacci
convergent* of `1/φ²` (`F₃/F₅`, with `F₃=NT, F₄=NS, F₅=d`), with higher
convergents `5/13, 13/34 → 1/φ²` (Cassini alternation, all PURE).

**Status — strong, φ²-coherent, modulus not yet forced.** The Fibonacci/φ²
identities are exact (PURE). `R_u = 1/φ²` matches at 0.17% (modulus) / 1.4%
(J) and shares the derived phase's `φ²` — far past a fit. Open: *why* the
apex modulus is exactly `1/φ²` (vs another φ-power). The open part shrank from
"unexplained `c/d`" to "why the apex is the `φ²` object", and `φ²` is already
atomic.

## Single-parameter apex + triangle predictions (2026-06-07)

Attempting to force `R_u` from the angle `γ`: **`γ` alone does not force `R_u`**
— a triangle is underdetermined by one angle (honest §5.4). But two facts
sharpen the picture:

1. **Single parameter.** `δ/π = R_u = 1/φ²`, i.e. **`δ = π·R_u`** — phase = π ×
   modulus. So the apex is `z = r·e^{iπr}` with one golden parameter `r = 1/φ²`;
   the two φ²-inputs collapse to one (`phase_over_pi_eq_modulus`, PURE via the
   shared Fibonacci convergents). Open: why `γ = π·R_u`, and why `r = 1/φ²`.

2. **The triangle is then determined and PREDICTS its other elements**
   (outputs, not inputs):
   - `β = 22.45°` vs observed `22.0°`
   - `sin 2β = 0.706` vs observed `0.695 ± 0.019` (**inside the error bar** —
     and `sin 2β` is the precisely-measured "golden mode" `B→J/ψ K_S`)
   - `α = 88.8°` vs observed `~85–90°`; `R_t = 0.932` vs `~0.91–0.93`

   So the φ²-apex is not just an η-fit: it reproduces the *independently
   measured* `sin 2β` within its error bar. (Trig values transcendental —
   documented, not PURE-Nat.)

## `1/φ²` grounded — the residue self-reference contracting eigenvalue (2026-06-07)

Why `1/φ²` (not an arbitrary golden power)? It is the **sub-dominant
eigenvalue of the residue's self-reference matrix** `M = [[c,1],[1,1]]` — the
Möbius `P` of `seed/AXIOM/05_no_exterior.md` §5.6 (`Mobius213`). Fully atomic
characteristic data (`JarlskogApex.apex_modulus_is_selfref_contracting_eigenvalue`,
PURE):

  `trace = c+1 = NS`,  `det = c−1 = 1`,  `disc = NS²−4 = 5 = NS+NT = d`,
  eigenvalues `(NS ± √d)/2 = φ², 1/φ²`.

So `R_u = 1/φ² = (NS−√d)/2` is the **contracting eigenvalue** (the rate `P^n`
converges to the residue fixed point φ). The value is structurally
distinguished, not fitted — the connection to §5.6 is the shared atomic
characteristic polynomial `x²−NS·x+1`, `disc = d`, not "φ appears in both".

## Sub-freedom REMOVED — `1/φ²` (not another golden power) is forced by `R_u < 1` (2026-06-08)

`JarlskogApex.apex_modulus_subunit_forced` (PURE). A residual worry was "why
this golden power `1/φ²`, not `φ`, `φ³`, …?". That sub-freedom is now closed:
the self-reference matrix `M = [[c,1],[1,1]]` has **exactly two** eigenvalues,
a **reciprocal pair** (`λ₊·λ₋ = det = 1`, `λ₊+λ₋ = NS`): `φ²` and `1/φ²`.
There are no other golden powers in `spec M`. The apex modulus `R_u` is a
unitarity-triangle side-ratio with the base normalised to 1, so `R_u < 1`
(observed ≈ 0.38). Of the reciprocal pair, **exactly one is `< 1`** — the
contracting `1/φ²`. Witnessed PURE by the Fibonacci convergents: `1/φ²`'s
(`2/5, 5/13, 13/34`) are sub-unit (`num < den`); `φ²`'s (`8/3, 21/8, 55/21`)
are super-unit (`> 2·den`). So *given the apex is a self-reference eigenvalue*,
`R_u < 1` forces `R_u = 1/φ²` uniquely. The open question collapses from
"which golden power" to the **single binary** physical premise below.

## RESOLVED (internally) — the CP-existence mechanism (2026-06-08)

`lean/E213/Lib/Physics/Mixing/ApexCPMechanism.lean` (4 PURE). A **213-internal**
derivation of the apex (no external flavour model), via the §5.7 frozen/dynamic
dualism of the self-reference map `M`:

  **`z = r·(−1)^r = r·e^{iπr}`,  `r = 1/φ²`,  `(−1) = M⁵`.**

- **Modulus** `R_u = r = 1/φ²` = the *frozen* (ℝ/hyperbolic) contraction
  eigenvalue — a real number, no phase.
- **Phase's `π`** = the *dynamic* (finite/A₅) reading's **half-period central
  involution** `M⁵ ≡ −I = e^{iπ}` (proven, `OrderFive`).
- **CP violation `η = r·sin(πr) ≠ 0` ⟺ `M⁵ = −1` (not `+1`)** — the falsifiable
  core. If `M⁵ = +I`, then `(+1)^r = 1`, the apex is **real**, `η = 0`, **no CP
  violation**. Because `M⁵ = −I` (a *proven* 213 theorem), CP violates. This is
  a *structural* reason, internal to 213.

This **answers the open premise** "why is CP-depth the self-reference
contraction rate": the apex *is* that contraction rate `r`, complexified by the
dynamic Lens's central element `M⁵ = −1`. The phase `δ = π/φ²` (previously only
*posited* in `CPViolation` as the number `176/147`, not derived) now has its
`π` grounded internally (`= M⁵`) and its `1/φ²` as the frozen contraction.

## Progress on the coupling route — the CP-area integer skeleton (2026-06-08)

`lean/E213/Lib/Math/Algebra/Icosahedral/SpanAreas.lean` (6 PURE). On the flagged
Pell-area ↔ CP route: the signed area spanned by two convergents `k` steps apart
is `det(v_m, v_{m+k}) = −F_{2k}`, position-independent (homogeneity from
`det M = 1`). The CKM apex is the **gen 1↔3 = two-step (k=2)** span, so its
integer span-area is `F₄ = NS = 3` — the **213-integer skeleton of the
unitarity-triangle CP-area `η̄/2`** (the conserved-area core of CP violation).
The adjacent (`k=1`) area is the Pell symplectic unit `−1` — the *same* `−1` as
the central `M⁵ = −1`, the two faces of `det M = 1`: the per-step symplectic
orientation and the half-period phase flip. CP needs both (nonzero area ×
nonzero phase).

This gives the CP-area its integer core but does **not** yet close the coupling:
the physical `η̄ ≈ 0.356` is `F₄ = NS` dressed by the λ-hierarchy and the
φ-contraction, and that dressing is not derived.

**The apex's spiral home (`SpanAreas` §4).** The apex convergent orbit sits on
the conserved **golden-norm hyperbola** `Q(m,k) = m²−m·k−k² = −1` (the `ℤ[φ]`
norm, discriminant `d = 5`) — the rotation invariant of the 213 P-spiral
(`Real213.SpiralRotationInvariant.Q_iterate_preserved`, conserved at every
turn). So the apex `z = r·e^{iπr}` is a point on the **self-reference P-spiral**,
whose `π` (half-period rotation, `M⁵ = −I`) is 213's own `PiCut` `π` and whose
golden-norm discriminant `5 = d` is the same `d` placing `M` in `SL(2,𝔽₅) ≅ 2I`.
Apex = spiral point + golden norm + icosian `π`, all 213-internal.

## What remains — the coupling `δ = π·R_u`, reframed as 0-parameter-forced

The single residual is the **coupling** `δ = π·R_u`. Note first it is *not* an
extra identity to bolt on: it **follows from the apex form** `z = r·(−1)^r`
(since `arg((−1)^r) = πr`, `|z| = r`). So the real question is *why the
exponent equals the modulus* (both `r`) — i.e. why the apex is the
**single-parameter** object `z = r·(−1)^r`.

**This is the `§5.1` no-exterior (0-parameter) principle applied to the apex
phase.** There is no exterior dialer, so the apex phase carries **no independent
degree of freedom** — it *must* be a function of the single internal number `r`
(the frozen contraction) and the only phase-bearing constant available, the
central involution's `π = arg(M⁵) = arg(−1)`. The minimal such realization,
linear in `r` with the central coefficient `π`, is `δ = π·r`. So the coupling is
**0-parameter-forced** (consistent with DRLT's whole no-free-parameter ethos),
not an arbitrary choice; both *ingredients* are internal (`r` frozen, `π = M⁵`
dynamic) and the **CP-existence mechanism is derived** (`η ≠ 0 ⟺ M⁵ = −1`).

**Honest residual.** What is *not* proven is the **minimality/uniqueness of the
linear form** `f(r) = π·r` (vs `π·r·(const)`, or higher order). The coefficient
being exactly `π` (one central half-turn, not `2π`) and the form being linear
are natural but not theorems. So the gap has shrunk from "why is the apex a
self-reference eigenvalue" (original) → "the phase is 0-parameter-forced to
`f(r)`; is the minimal linear `π·r` the forced form?" — a soft, well-isolated
residual, with the structure, mechanism, and 0-parameter status all internal.

### Three convergent framings of the coupling (synthesis)

The coupling `δ = π·R_u` is read three ways, all 213-native, all consistent:

1. **Form-consequence.** `δ = π·R_u` *follows* from the apex form `z = r·(−1)^r`
   (`arg((−1)^r) = πr`); the question is the single-parameter form (exponent =
   modulus).
2. **§5.1 no-exterior.** The apex phase has no independent dialer, so it must be
   `f(R_u, π=arg M⁵)`; `δ = π·R_u` is the minimal linear realization
   (0-parameter-forced).
3. **§5.7 frozen=dynamic (suggestive, NOT forcing — honest correction).** It is
   *tempting* to read `δ/π = R_u` as the frozen=dynamic identity (frozen
   contraction = dynamic phase-fraction, the same residue two ways). **But this
   does not force the coincidence**: the *per-step* rates genuinely **differ** —
   frozen contraction is `1/φ²` per step, dynamic phase is `1/5` per step
   (`M⁵=−I` over 5 steps), and `1/5 ≠ 1/φ²`. So §5.7 ("both readings hold")
   does *not* imply the two extracted numbers agree. `JarlskogApex.phase_over_-
   pi_eq_modulus` is just **Fibonacci arithmetic** (`2/5, 5/13` are what they
   are); reading them as "both = `δ/π` and `R_u`" *assumes* `δ=π/φ²` (which
   `CPViolation` **posits** as `176/147`, not derives). So `δ/π = R_u` remains
   the **single-parameter posit/ansatz**, not a PURE-forced identity.

**The spiral-trajectory reading is RULED OUT (PURE).**
`ApexCPMechanism.coupling_not_uniform_spiral`: the apex is *not* `n` steps of a
uniform discrete spiral (phase `nπ/5`, modulus `(1/φ²)ⁿ`) — the phase-fraction
`1/φ²` lies strictly between the consecutive steps `1/5` and `2/5`
(`1/5 < 8/21 ≤ 1/φ² ≤ 5/13 < 2/5`), so no integer step realizes it, and the
fractional `n=5/φ²` gives the wrong modulus. So the `π/5`/`2π/5` angle-fishing
routes are now *proven* dead (not just flagged): the coupling is the **§5.7
coincidence** (two readings of one residue both `= 1/φ²`), not a trajectory.

**Honest net (after self-correction).** What is PROVEN: `R_u = 1/φ²` grounded
(contracting eigenvalue); `M ∈ A₅/2I`; the spiral-trajectory reading RULED OUT;
`π` 213-internal; all *ingredients* internal. What is **posited**: `δ = π/φ²`.

## ★ RIGOROUS RESULT — `δ` is NOT an A₅ quantity (2026-06-08)

Attacking "derive `δ` from the A₅ 3-rep mass structure" (agent team: A₅+gCP
literature + explicit 3-rep computation) gave a decisive **negative**
(`Icosahedral/A5RealityNoCP.lean`, 4 PURE):

- **The A₅ 3-rep is a REAL representation** (Frobenius–Schur indicator `+1`;
  `A₅ ⊂ SO(3)` is *the* icosahedral rotation group). The golden ratio **cancels**
  in the FS indicator: `12·(1−φ) + 12·φ = 12` (integer), `FS·60 = 3+45+0+12 = 60`.
- A real rep ⟹ A₅-invariant mass matrices are real-symmetric ⟹ real CKM ⟹
  **Jarlskog `J = 0`** — *no CP* from A₅ alone (verified: the golden mixing
  matrix `U_GR` is real, `J(U_GR) = 0`).
- With generalized CP (gCP), the Dirac phase **quantizes** to
  `δ_CP ∈ {0°, 90°, 180°, 270°}` (trivial or maximal) — **never golden**
  (Di Iura–Hagedorn–Meloni 1503.04140; Turner 1506.06898, Table 1). `π/φ²=68.75°`
  and `2π/5=72°` are **not** predicted phases; `68.75°` is not a clean
  icosahedral angle either (nearest: `arccos(1/√5)=63.4°`), and is a mediocre
  fit (observed `γ≈65.7°`).

**So `δ = π/φ²` is NOT derivable from A₅ — and A₅ actively gives a different
answer** (real / CP-conserving, or maximal `90°` with gCP). In A₅, `φ` is a
**(real) mixing-angle** quantity (`tan θ₁₂ = 1/φ`), and the CP phase `δ` is a
**(complex) phase**, group-theoretically *distinct*. DRLT's `δ = π/φ²` conflates
the two. The apex therefore splits honestly:

| part | status |
|---|---|
| **modulus `R_u = 1/φ²`** | grounded — the real golden eigenvalue of `M` (a mixing-magnitude quantity, exactly where A₅'s `φ` lives) |
| **phase `δ = π/φ²`** | **posit** — NOT an A₅ consequence; needs a genuinely complex mechanism (the self-reference complexification `−1=M⁵ ↦ e^{iπ}`, itself a posit), distinct from the real A₅ flavour mixing |

So the open premise is now precisely located: it is **only** the *phase* `δ`,
and the A₅/golden route to it is **closed** (A₅ gives no golden phase).

### ★ Icosian/2I route also CLOSED (agent computation, 2026-06-08)

The binary-icosahedral `2I`/`600`-cell/`E₈` structure produces only
**`π/5`-quantized angles** `{36, 60, 72, 108, 144, 180, 216, 240, 288}°` — all
*rational* multiples of `π`. The order-10 icosian (`M⁵=−1`) is a `72°=2π/5`
rotation; the `2I` 2-dim spinor irreps force phases `{36,108,252,324}° = k·π/5`.
**`π/φ²=68.75°` is an *irrational* multiple of `π`** (`φ²` irrational), so it
**cannot** be any icosian angle/phase — a *structural* impossibility, not a
numerical miss. This is the deeper meaning of `coupling_not_uniform_spiral`
(`δ/π = 1/φ² ∈ (1/5, 2/5)`): `δ` is **off the icosian `π/5` phase-lattice**
(`5/φ² = 1.91 ∉ ℤ`). Nearest icosian phase: `72°` (gap `3.25°`); the icosian
structure, if it forced `δ` at all, would give `36°` or `72°`, not `π/φ²`.

Golden-but-not-icosian closed forms near the posit: `arctan(φ²) = 69.095°`
(gap `0.35°`), `arccos(1/φ²) = 67.54°` — separate golden constructions, **not**
group-grounded.

### ★ CD-tower route also CLOSED (agent computation, 2026-06-08)

The Cayley–Dickson tower (`CayleyDickson/`) and the CP-phase machinery
(`Mixing/`) are **architecturally disjoint** (no `Mixing` file imports CD). CD's
complex structure (`ℂ=ℤ[i]`, `ℤ[ω]`) carries only **discrete** phases — the
cyclotomic unit groups `C₄` (`90°`, `ℤ[i]`) and `C₆` (`60°,120°`, `ℤ[ω]`); no
derived continuous `U(1)`/argument. The `d=5` golden `ζ₅=e^{2πi/5}` does **not**
appear as a CD unit (the icosian `ℤ[φ]` is a *real* quadratic field). So CD gives
`π/2`- and `π/3`-quantized phases, again **not** `π/φ²`.

**The hard obstruction (named):** `A5RealityNoCP.a5_3rep_is_real` (`FS=+1`) is a
*wall* — the `d=5` golden structure puts `ζ₅` into the (real) **mixing angle**,
the phase cancelling. Any CP mechanism must break this reality via a
**complex-type (`FS=−1`) representation wired to the 3 generations** — which no
current 213 structure (real `A₅`, real-quadratic icosian `ℤ[φ]`, generation-
disconnected complex `ℤ[i]/ℤ[ω]`) provides.

### ★ The coherent conclusion (3 independent agent routes)

| 213 structure | forced phases | `π/φ²`? |
|---|---|---|
| A₅ + gCP | `{0,90,180,270}°` (`π/2`·ℤ) | ✗ |
| Icosian / `2I` / E₈ | `{36,72,108,…}°` (`π/5`·ℤ) | ✗ (off-lattice) |
| CD tower (`ℤ[i],ℤ[ω]`) | `C₄=90°`, `C₆=60,120°` (`π/2,π/3`·ℤ) | ✗ |

**Every 213 discrete/cyclotomic structure forces a phase that is a *rational*
multiple of `π` (a root of unity). `π/φ²` is an *irrational* multiple of `π`.**
So `δ = π/φ²` is provably **not** a discrete-symmetry/cyclotomic phase — it is a
golden-*arithmetic* posit, not a group-theoretic angle. Routes proven dead:
A₅-golden, icosian `π/5`, CD `C₄/C₆`, spiral, `π/5`, `2π/5`.

**What this forces (the real fork):** either **(a)** `δ = π/φ²` is the wrong
posit and the genuine 213 CP phase is a *quantized* value (`90°` = right
unitarity triangle, from `C₄`/CD `i`); or **(b)** new non-discrete infrastructure.

### ★★★ RESOLUTION (KM-mechanism agent + synthesis, 2026-06-08) — option (a)

The KM-mechanism agent closed it via **Niven's theorem**: a discrete-symmetry CP
phase has rational cosine, allowed only at `0°,60°,90°` — so it is a **root of
unity**, and **a golden (`φ`-valued) phase is impossible from any discrete
structure**. `δ = π/φ²` (cos irrational) is Niven-**forbidden** as a discrete
phase. The empirical special value is `α ≈ 90°` (UTfit `α = 92.4°±1.4°`; the
"right unitarity triangle" / maximal-CP program).

**So the apex reframes** (`Mixing/ApexRightTriangle.lean`, 5 PURE): the CP phase
is the **CD imaginary unit `i`** (the `NT=2` first doubling, `ℤ[i]^× = C₄`,
`arg i = π/2`) ⟹ **`α = 90°`** (right triangle), and the golden ratio is the
**modulus** `R_u = 1/φ²` (derived `M`-eigenvalue), NOT the phase. Then the apex
on the Thales circle gives the clean output

  **`cos γ = R_u = 1/φ²`,  `γ = arccos(1/φ²) = 67.54°`,  `β = 22.46°`,  `α = 90°`.**

| element | predicted | observed |
|---|---|---|
| `β` | `22.46°` | `22.5°±0.7°` ✓ ≈exact |
| `γ` | `67.54°` | `65.1°±1.5°` (~1.6σ) |
| `α` | `90°` | `92.4°±1.4°` (~1.7σ) |
| `η̄` | `0.353` | `0.347±0.010` |
| `ρ̄=R_u²` | `0.146` | `0.161±0.010` (~1.5σ) |

**Two principled inputs** — the quantized phase `α = π/2` (CD `i`, Niven-allowed)
+ the golden modulus `R_u = 1/φ²` (derived) — fix the triangle, with `cos γ=1/φ²`
a clean golden output and `β` essentially exact. This **replaces** the single
Niven-forbidden golden-phase posit `δ = π/φ²`. Honest: `α=90°` is still an input
(motivated by CD `i` / right-triangle, not forced); fit is ~1.5σ (decent, not
perfect). The advance is **principled-ness** — the phase is a Niven-allowed root
of unity consistent with *every* no-go (A₅ real, icosian `π/5`, CD `C₄/C₆`,
Niven), rather than a structurally-impossible golden phase.

**Marathon verdict.** `δ = π/φ²` is demoted (Niven-forbidden golden phase). The
213-coherent CP structure is **golden modulus + `π/2` phase** (`cos γ = 1/φ²`).
What *is* derived: CP **existence+uniqueness** (`CPPhaseCount`: `N_gen=3 ⇒ 1`
phase) and the golden **modulus** (`R_u=1/φ²`). What is an input: the `α=90°`
phase (principled via CD `i`, but a posit). Full synthesis:
`research-notes/cp_phase_origin_synthesis.md`.

**Correction (`π` is 213-internal).** An earlier note here called the `π`
coefficient "the transcendental tail outside 213 / the Nat boundary" — that was
an **overclaim**. `213` constructs `π` as a `Real213` cut (`PiCut`, a Wallis
`AbCutSeq`, `π ∈ (14/5,4)`, ∅-axiom), so `δ = π/φ²` is a product of **two
213-internal cuts** (`π` and `1/φ²`) — the apex is internal *including* `π`
(`ApexPiInternal.lean`: `δ ∈ (112/105, 20/13) ∋ 176/147`, PURE). Moreover the
phase's central `−1 = M⁵` is the **binary-icosahedral `2I` central quaternion**
over `ℤ[φ]` (`MobiusPIcosian`: `SL(2,𝔽₅) ≅ 2I`, the `E₈` icosian endpoint), so
the `π` is the icosian rotation structure's, golden-native. The apex derivation
is 213-internal **end-to-end**; the only residual is the continuum form-
minimality of `f(r) = π·r`, not any escape from 213.

## (superseded) What remains — one physical identification

The *value* `1/φ²` is now fully atomic-grounded (contracting self-reference
eigenvalue) **and** the golden-power sub-freedom is forced away (above). The
single remaining open premise: **why the CKM CP-apex modulus is a
self-reference eigenvalue at all** — why CP-violation depth = the residue's
self-reference contraction rate. One clean structural identification (not a
fitted number); it would pin the apex (`γ = π·R_u` is the other face of the
single-parameter apex `z = r·e^{iπr}`), making `J = A²λ⁶η` atom-pinned and
resolving θ_QCD's `J`.

### Sharpened mechanism to pursue (concrete, not yet derived)

The cleanest *structural* form of the open premise — the next real step (not
another % match): the three quark generations are three layers of the `M`-
iteration (Mobius213 shows layers 0–8 = even/odd Fibonacci = the convergent
trajectory). The apex `R_u = |V_ud V_ub|/|V_cd V_cb| ≈ |V_ub|/(λ|V_cb|)`
compares the gen-1→3 reach to the gen-2→3 reach — a **one-generation-step**
difference. If each generation step contracts the inter-layer reach by the
self-reference eigenvalue, then after stripping the Wolfenstein λ-hierarchy the
residual 1→3-vs-2→3 shape factor is **one** contraction step = `1/φ²`. This is
a testable mechanism (pin "generation = M-layer" and the apex follows), not yet
a theorem — the honest concrete target replacing the law-of-sines fishing route.

## Honest numerical status against CURRENT fits (2026-06-08)

Re-checked against current PDG/CKMfitter (deep-research sweep). The φ²-apex is
strong on the **imaginary side**, weaker on the **real side**:
- `R_u = 1/φ² = 0.382` vs `√(ρ̄²+η̄²) ≈ 0.384–0.394` — **0.5–3%** (was 0.17%
  vs the older central value; current global ρ̄ is higher, widening this).
- `η̄ = 0.356` vs `0.348–0.357` — **good** (≤2.3%).
- `ρ̄ = (1/φ²)cos(π/φ²) = 0.138` vs `≈ 0.14–0.16` — **weaker** (up to ~13% vs
  the higher current global ρ̄≈0.16; fine vs older ρ̄≈0.141).
- `sin 2β = 0.706` vs CKMfitter `0.684 ± 0.022` — **~0.6–1.0σ high**, NOT
  "inside the error bar" as previously logged (corrected here and in
  `JarlskogApex.lean` §4). Consistent but systematically on the high side
  (γ = π/φ² = 68.75° is likewise ~1σ above the global γ ≈ 65–66°).

Net: the apex *modulus/η̄* match survives at the few-% level; the *phase-side*
predictions (γ, sin2β) run ~1σ high. This is a real, honest tension to carry,
not a closed precision result.

## External anchor + novelty (deep-research, 2026-06-08)

- **Golden-ratio flavour mixing is an established, peer-reviewed line — for
  LEPTONS.** `cot θ₁₂ = φ` / `cos θ₁₂ = φ/2` from **A₅ (icosahedral) flavour
  symmetry** (Feruglio–Paris arXiv:0705.4559; JHEP 03(2011)101;
  arXiv:0812.1057, 1110.1688). A golden **Cabibbo** angle also exists
  (`θ_C = π/4 − θ₁₂ = 13.3°`, quark-lepton complementarity) — consistent with
  DRLT's `λ = 5/22` (θ_C = 13.1°). So DRLT's golden approach sits inside a
  live (heterodox but respectable) research area, not in isolation.
- **No precedent for a golden CP-apex.** Multiple targeted searches found
  **nothing** connecting the golden ratio to `δ_CP` or the unitarity-triangle
  apex modulus (the golden-mixing literature is solar-angle / Cabibbo only;
  CP-phase work is *geometric* but not golden). So DRLT's `δ = π/φ²` +
  `R_u = 1/φ²` are **novel** — strong pre-registration priority value (deposit
  externally per `PRE_REGISTRATION.md`).
- **Research lead.** A₅/icosahedral is *the* known origin of golden mixing, and
  φ lives in A₅'s geometry. Open question worth a session: does the residue
  self-reference map `M = [[c,1],[1,1]]` (§5.6) connect to A₅ — i.e. is DRLT's
  φ² the *same* φ that A₅ flavour symmetry produces, via a shared icosahedral
  structure? That would bridge the DRLT mechanism to established flavour physics.

## Marathon result — the self-reference map IS an A₅ element (2026-06-08)

The research lead above is now **substantially answered at the group-theory
level** (`lean/E213/Lib/Math/Algebra/Icosahedral/`, 14 thms PURE):

- `M` reduced mod `d = 5` satisfies `M⁵ ≡ −I (mod 5)`, `M¹⁰ ≡ I`, with order
  **exactly** 5 in `PSL(2,𝔽₅) ≅ A₅` (the whole mod-5 orbit computed by genuine
  𝔽₅-matrix multiplication, `OrderFive.order_exactly_five_in_psl` — closes the
  "no early return" gap that `Mobius213ModFive`'s precomputed-entry statement
  left open). So `M` is a **5-fold icosahedral rotation**.
- That A₅ element carries the icosahedral 3-rep **character `φ`**; `M`'s ℝ
  eigenvalue is `φ²`; they are **one** golden ratio, bridged by `φ² = φ + 1`
  = the Fibonacci recurrence on convergents (`A5Bridge.golden_bridge`:
  `eigenvalue = character + 1`).
- `d = 5` is **both** `disc M = NS²−4` (ℝ side) **and** the field `𝔽₅`
  realising A₅ (`OrderFive.d_double_role`).

**What this changes for the open premise.** "Why is the CP-apex modulus a
self-reference eigenvalue" now has a concrete *structural home*: the
self-reference map is literally an `A₅` rotation. **Honest scope correction
(2026-06-08, deep-research):** the established `A₅`/`SU(5)×A₅` flavour models
(arXiv:1410.2057, 1312.0215) do **not** golden-*predict* the quark CKM apex —
at leading order their CKM is `≈ identity + Cabibbo`, and the apex/CP phase is
obtained by **numerical fit** of subleading terms (a trivial-identity CKM is the
generic leading-order result of *any* discrete flavour group once residual
symmetries coincide). So `A₅` supplies the *group-theoretic home* of `φ`, but
**no existing flavour model derives `R_u = 1/φ²`** — DRLT's golden apex is novel
relative to the entire flavour-model literature (priority-strengthening, not
priority-borrowing). The nearest *established* prediction is the **nearly-right
unitarity triangle** (`α ≈ 89–90°`, `δ ≈ 1.188 ± 0.016 rad`) from discrete
symmetry + a `π/2` mass-matrix phase (arXiv:1805.07773, 1103.5930); DRLT's
`δ = π/φ² = 1.200 rad` is concordant with it at **0.75σ**, and `α = 88.8°` is
near (not exactly) `90°`.

**Still open (honest, §5.4).** This is a *bridge*, not a closure: it shows `M`
is an A₅ element carrying `φ`, but does **not yet derive** the apex *value*
`R_u = 1/φ²` from an explicit `A₅` flavour assignment of the three generations.
The next real step: build the `A₅`-triplet assignment of the quark generations
and read off the mixing apex — comparing against the established `SU(5)×A₅`
model. That would convert the bridge into a derivation.

## Flavour-layer marathon — A₅ rep data + golden-mixing template built (2026-06-08)

Continued the marathon into the `A₅` flavour-symmetry layer
(`Icosahedral/A5Reps.lean`, `GoldenMixing.lean`, +9 PURE; tree now 23/0):

- **A₅ rep data** (`A5Reps`): irrep dims `Σdim²=60`; Clebsch–Gordan dims —
  notably **`5⊗5 = 25 = d²`** decomposing as `1⊕3⊕3'⊕4⊕4⊕5⊕5`, i.e. DRLT's
  channel count `25` is an `A₅` Clebsch sum. The triplet character
  orthonormality `χ²(5A)+χ²(5B) = φ²+1/φ² = NS = trace M` — the `A₅` flavour
  orthonormality and the self-reference trace are **one** golden invariant.
- **Golden-mixing template** (`GoldenMixing`): the established `A₅` lepton
  result `cot θ₁₂ = φ ⇒ sin²θ₁₂ = 1/(φ²+1) ≈ 0.276` (Fibonacci-bracketed
  `8/29 < · < 5/18`), `tan²θ₁₂ = 1/φ²` — the **same `1/φ²`** as the apex
  candidate, here arising as the eigenvector overlap of the order-5 generator
  `M`. So the *mechanism* "order-5 generator → golden mixing angle" is pinned.

**Net.** The `A₅` infrastructure (reps, Clebsch, character, mixing template)
now exists PURE. The open premise is sharpened to its final form: the lepton
solar-angle template `sin²θ₁₂ = 1/(φ²+1)` is the established `φ→angle`
mechanism; the **quark CKM CP-apex** `R_u = 1/φ²` is the analogous construction
*in the quark sector with the CP phase* — the same `1/φ²` appears as `tan²θ₁₂`,
but mapping it to the apex needs the quark `A₅` assignment + CP, still open.

## Tested and NOT closed — the law-of-sines route (honest, fishing-risk flagged)

Attempt: if all three triangle angles are atomic, law-of-sines forces `R_u`.
We have `γ = π/φ²`. The second angle `β ≈ π/8` (atomic candidate: `8 = NS²−1`,
the gluon-octet count) gives, with `γ`, `R_u = sin β / sin α = 0.38278` —
matching the Möbius eigenvalue `1/φ² = 0.38197` to **0.2%**.

**But this does NOT close the identification, and is flagged as
approximation-stacking:**
- `β = π/8 = 22.5°` is itself only a **2.2%** match to observed `β = 22.01°`
  (from `sin 2β = 0.695`) — no better than other candidate-level matches.
- The 0.2% agreement between the law-of-sines value and the Möbius eigenvalue
  holds *only if* `β = π/8` exactly; given the 2% slop, the agreement may be
  partly coincidental.
- Finding several atomic readings that all roughly fit (`c/d`, `1/φ²`, `π/8`,
  law-of-sines) is the **multiple-comparisons fishing** risk
  (CLAUDE.md). None of these is a derivation.

**Conclusion (§5.4):** the *value* `R_u = 1/φ²` is solidly grounded (Möbius
contracting eigenvalue, PURE). The *physical identification* — why the CKM
CP-apex modulus equals the residue self-reference contraction rate — was
genuinely looked for and is **not derivable this session**; it remains the
single open premise. Do not re-fish atomic-angle combinations; the next real
step is a *structural* reason CP-violation depth = self-reference contraction,
not another % match.

## Anchors

- `lean/E213/Lib/Physics/Mixing/JarlskogApex.lean` — apex = φ² object, self-ref eigenvalue; §5.5 `apex_modulus_subunit_forced` (1/φ² forced by R_u<1)
- `lean/E213/Lib/Physics/Mixing/ApexCPMechanism.lean` — **internal apex derivation**: `z=r·(−1)^r`, CP ⟺ `M⁵=−1`; frozen modulus + dynamic central involution
- `lean/E213/Lib/Physics/Mixing/A5QuarkApex.lean` — two-origin CKM: Cabibbo 5/22 rational (not golden) vs apex 1/φ² golden; honest "A₅ models fit not predict" + right-UT concordance
- `lean/E213/Lib/Math/Algebra/Icosahedral/` — M is an order-5 A₅ element; golden character ↔ eigenvalue bridge; A₅ rep data + golden-mixing template (INDEX.md)
- `lean/E213/Lib/Math/Algebra/Mobius213.lean` — the §5.6 self-reference matrix, eigenvalues φ²,1/φ²
- `lean/E213/Lib/Physics/Mixing/CPViolation.lean` — J structure + magnitude-gap note
- `lean/E213/Lib/Physics/Mixing/CKMHierarchy.lean` — λ, A = φ/c, s₂₃, s₁₃
- `lean/E213/Lib/Physics/Mixing/CabibboAngle.lean` — λ = 5/22
- `lean/E213/Lib/Physics/Couplings/ThetaQCD.lean` — the θ_QCD consumer of J
</content>

## ★ "phase ∈ C₄" premise CLOSED (2026-06-08, SignedStarFull)

The last CP-phase premise is now forced. `Cohomology/Hodge/SignedStarFull` (6
PURE) lifts the signed Hodge star to the full grade-1 space `Λ¹(ℝ⁴)` of the
`(d−1)=4`-dim simplex (diagonal: forward signs `(+1,−1,+1,−1)`, back `(−1,+1,−1,
+1)`), showing `⋆²=−1` on ALL of `Λ¹` ⇒ `⟨⋆⟩` order *exactly* 4 = `C₄` (not `C₆`).
So "phase ∈ C₄" (`CPPhaseC4Forcing`) is not assumed — the Hodge structure on the
`d=5` cohomology IS the `C₄`, hence the phase is `90°`. Remaining open: the
explicit `5̄⊕10` generation Yukawa from first principles; the ~1.5σ fit
(irreducible, principled-ness over precision).

---

## ★★★ Multi-agent deep-dive (2026-06-08) — "why exactly 1/φ², is it the right value?"

Four-agent investigation (repo archaeology + geometry + live data + theory).
Net: the **value is structurally forced; the open part is one physical arrow; and
the golden-ness is in the radius, not the angle**.  Five concrete findings.

### 1. The value is canonical, not reverse-engineered (archaeology)
`M=[[2,1],[1,1]]` is the **algebraic encoding of the 213 axiom itself**
(`seed/AXIOM/03_form.md §3.5`, ∅-axiom `Mobius213.lean`): trace `=NS=3`, det `=1`,
disc `=NS²−4 = 5 = NS+NT = d`, eigenvalues `(NS±√d)/2 = φ², 1/φ²`.  `M = Q²` with
`Q=[[1,1],[1,0]]` the Fibonacci matrix (`FibonacciAtomicLock.P_eq_Q_squared`); also
`M = R·L` (Stern–Brocot).  It appears in 17+ non-physics files (self-reference,
Moufang-failure rate, Nat construction) **before** any CKM use.  So `R_u=1/φ²`'s
forcing is real.

### 2. The primitive form is `(NS−√d)/2`, not "1/φ²" (theory)
Per "give meaning to nothing": `(NS−√d)/2 = (3−√5)/2` imports only the atomic
counts + the quadratic formula; "1/φ²" smuggles the golden-ratio *name*.  Commit to
`R_u = (NS−√d)/2`; "1/φ²" is the derived golden *reading*.  It also exposes the
load-bearing coincidence **disc = NS²−4 = NS+NT = d**, true *only* at `(NS,NT)=(3,2)`
(`9−4=5=3+2`) — a sub-question: selection or accident? (cheap finite check, do first.)

### 3. CORRECTION — `1/φ²` is the eigenvalue, NOT the convergence rate
The repo gloss "`1/φ²` = rate `P^n→φ` converges" is imprecise.  The Möbius
multiplier at the fixed point is `P′(φ)=1/(φ+1)²=1/φ⁴` (the eigenvalue *ratio*
`λ₋/λ₊`), a distinct quantity.  `1/φ²` is the contracting *eigenvalue* `λ₋` of the
reciprocal pair `λ₊λ₋=det=1`.  (Fixed in `JarlskogApex.lean §5` docstring.)

### 4. Why a SQUARE (modulus/de-signed-step) — the genuinely structural reason
`M=Q²`.  One Fibonacci step has eigenvalues `φ, −1/φ` — the `−1/φ` is **signed**
(the difference-Lens Bool readout).  Squaring kills the sign → `1/φ²` (positive).  A
**modulus** is sign-free, so the apex *modulus* must be `1/φ²` (two-step, de-signed),
**not** `1/φ` (one-step, negative): a modulus cannot equal a negative one-step
eigenvalue.  The square is forced by "it's a modulus."  **Now ∅-axiom**
(`Mobius213/Px/FibonacciAtomicLock.apex_modulus_is_designed_square`): `det Q = −1`
(signed), `det P = (det Q)² = +1` (de-signed) ⟹ the contracting eigenvalue is
positive (its own modulus) only at the `Q²` level (`1/φ²`); plus Vieta reciprocity
(`λ₊λ₋ = det = 1`, `λ₊+λ₋ = trace = NS`) — the base-normalization data.

### 5. The arrow to close the gap — `det=1` ↔ base-normalization
The one missing step (candidate→theorem): *why the apex modulus = `λ₋` specifically*.
Most promising route: `M` is unimodular (`det=1`) ⇒ reciprocal pair `λ₊λ₋=1`.  The
unitarity triangle normalizes one leg (cb) to `1`.  Reciprocity (`λ₊λ₋=1`) **is**
base-normalization (one leg ≡ `1` carries `λ₊`), forcing the **apex** to carry `λ₋`.
Pure algebra (`det=1`), no fitting.  Build: express CKM in `M`'s eigenbasis and show
the 1–3 (apex) sector inherits `λ₋`.

### 6. Live-data verdict (UTfit/HFLAV 2024, fetched) — radius confirmed, can't resolve form
`R_u = 0.3812 ± 0.0090` (UTfit Summer-2024), `0.3797 ± 0.0130` (HFLAV PDG-2024).
`1/φ² = 0.38197` is **+0.08σ / +0.17σ** — consistent with *exactly* `1/φ²`.  Caveats:
- Data **cannot distinguish** `1/φ²` from convergents `8/21, 13/34, 21/55` (cluster
  within 0.15σ; need ~20× tighter `σ_Ru`).  And higher convergents do **not** fit
  better — the limit sits closest to center (the "more-resolved = better" intuition
  is wrong; convergents oscillate around the limit).
- The match is a **global-fit** property.  Raw `|Vub/Vcb|` (incl or excl) gives
  `R_u=0.40–0.42` (1–1.5σ high); the `|Vub|` incl/excl puzzle (~2–3σ) is a ~5%
  irreducible systematic.  Inclusive `|Vub|` is *worse* for `1/φ²`.

### 7. Limit vs convergent — resolved by presentation-invariance
`1/φ²` (the exact root) is the right object **because the eigenvalue is
presentation-invariant** (exact in `M`'s eigenbasis, no iteration needed), while a
finite convergent `Pⁿ(x₀)` is presentation-dependent (depends on `n`, seed `x₀`).
By the repo's own `PresentationDependence` logic the invariant object is the real.
NOT "irrational so untouchable" — that would be the Real213-as-shield failure mode.

### ★ Recommendation (the sharpest 213 position)
**Decouple radius from angle.**
- **Tier-1 (near-exact, forced-value):** `R_u = (NS−√d)/2 = 1/φ²` — the golden
  *radius*.  `+0.1σ`.  Open arrow: finding (5).
- **Tier-2 (separate, falsifiable, currently ~−1.6σ):** `α=90°` (right triangle,
  from the proven Hodge `C₄`/`⋆²=−1`) ⟹ `ρ̄ = R_u² = 1/φ⁴ ≈ 0.146` vs observed
  `ρ̄≈0.159`.  The `O(λ²)` Wolfenstein correction does **not** cure it (moves `ρ̄`
  to `0.142`, wrong way).  With the *observed* `γ≈66°`, `R_u=1/φ²` reconstructs
  `ρ̄=0.156, η̄=0.349` perfectly — so the angle is non-golden (`arccos(1/φ²)=67.5°`
  is **not** a golden angle 36/72/108).
Do **not** bundle a golden *length* with a non-golden *right angle*; the bundle
hides the `ρ̄` tension and ties the program's strongest result (radius) to its
weakest (α=90°).  State `ρ̄=1/φ⁴` loudly as the Tier-2 falsifier.
