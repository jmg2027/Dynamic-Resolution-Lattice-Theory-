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

## What remains — one physical identification

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
self-reference map is literally an `A₅` rotation, and `A₅` golden-ratio flavour
symmetry (`SU(5)×A₅`, arXiv:1410.2057, 1312.0215) is established physics that
reproduces quark mixing + the CP phase from this same `φ`. DRLT already has the
`SU(5)` side (`d=5`, `5⊗5=25`); it now has the `A₅` side *as the same matrix*.

**Still open (honest, §5.4).** This is a *bridge*, not a closure: it shows `M`
is an A₅ element carrying `φ`, but does **not yet derive** the apex *value*
`R_u = 1/φ²` from an explicit `A₅` flavour assignment of the three generations.
The next real step: build the `A₅`-triplet assignment of the quark generations
and read off the mixing apex — comparing against the established `SU(5)×A₅`
model. That would convert the bridge into a derivation.

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
- `lean/E213/Lib/Math/Algebra/Mobius213.lean` — the §5.6 self-reference matrix, eigenvalues φ²,1/φ²
- `lean/E213/Lib/Physics/Mixing/CPViolation.lean` — J structure + magnitude-gap note
- `lean/E213/Lib/Physics/Mixing/CKMHierarchy.lean` — λ, A = φ/c, s₂₃, s₁₃
- `lean/E213/Lib/Physics/Mixing/CabibboAngle.lean` — λ = 5/22
- `lean/E213/Lib/Physics/Couplings/ThetaQCD.lean` — the θ_QCD consumer of J
</content>
