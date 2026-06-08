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
