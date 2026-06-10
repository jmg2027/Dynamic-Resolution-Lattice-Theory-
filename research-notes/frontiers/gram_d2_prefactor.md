# Frontier — the Gram correction's `/d²` prefactor

**Status**: OPEN. **Domain**: physics (α_em deployment).
**Opened**: 2026-06-07.

## The reduced problem

The Gram self-consistency cubic `25·y³ + 1 = 25·X·y²` is **not** an
independent modeling choice: `GramCubicReduction.cubic_is_correction_ansatz`
(PURE) shows it is the algebraic re-expression of the correction ansatz

  `correction = X − y = 1/(25·y²) = α²/d²`   (d² = 25, α = 1/y).

So the only residual `modeling-form` degree of freedom in the α_em Gram
layer is: **why is the correction `α²/d²`?**

- `α²` — structurally expected: a self-energy correction is `O(α²)`.
- `/d²` (the `25 = d²` prefactor) — **the open item**.

## Why it is not yet closed (honest boundary, §5.4)

The `d² = 25` prefactor currently has **three candidate readings** but no
forcing theorem selecting one:

1. **block-pair total** — `d²` pairs of the atomic structure;
2. **Gram matrix DOF** — the dimension of the relevant Gram matrix;
3. **α_GUT factor** — `1/α_GUT = d²·ζ(2)` (`Couplings.AlphaGUT`).

`Augmented.lean` § GramSelfEnergy lists all three as "readings."
`GramSelfConsistency.lean` lists "cohomological derivation of the d²
prefactor" as a Step-4+ open item. `CupRingTrace.lean` is, by its own
header, a **bottom-up test** (functionals defined first, result observed
second), not a forcing derivation. So the cup-ring trace does **not**
currently force the prefactor.

## Progress — the *value* is over-determined (2026-06-07)

`GramD2Readings.lean` (PURE) consolidates the three candidate readings:
`fullDimSquared`, `gramMatrixEntries`, and `inv_alpha_GUT_factor` all equal
`d² = 25` (`three_readings_coincide`, `all_readings_are_d_squared`), with
the block-pair reading given content via `d² = d + 2·C(d,2)` (`25 = 5+2·10`,
`blockpair_decomposition`). So the three are **not competing choices** —
they are facets of one structural quantity `d²` (equivalence-pluralism
discipline). The open question narrows: **not** "which value", but "which
*mechanism* links the self-energy to `d²`".

## Mechanism — IDENTIFIED (2026-06-07)

`GramD2Mechanism.lean` (PURE) identifies the mechanism by connecting two
**independent math-side structures** that both yield `d²` for a
**degree-2 (2-point)** object on the `d = 5` state space:

1. **2-point operator-space dimension** — a self-energy is a 2-point
   function in `V ⊗ V ≅ End V`; `tensorDim d d = d²`
   (`Lib/Math/Algebra/Linalg213/Gap/TensorProduct`, `5⊗5=25` = K_{3,2}
   channel count).
2. **2-fold cup-graduation denominator** — the self-pairing `k=1` cup term
   carries denominator `d^(k+1) = d²`
   (`RefinedCupLadderDerivation.cup_graduation_denom`).

These **coincide** (`mechanisms_converge`): a degree-2 object normalizes by
`d²`, read two independent ways that agree. Combined with the forced
numerator `α²` (self-energy is `O(α²)`), this grounds `correction = α²/d²`
in degree-2 structure — not a posit.

**Remaining premise** (the now-narrow open part): the identification of the
Gram self-energy *with* the degree-2 / 2-point cup object — the natural
reading of a self-energy, but not yet a separate forcing theorem.

## Reframe — "it's not Gram" (2026-06-07, originator's insight)

Testing the "Gram" label against `Lib/Math/Algebra/Linalg213/Gram.lean`:
a genuine Gram matrix is **symmetric** (`inner_symm`) with **rank ≤ d**
(stated, line 15). So its independent DOF is *not* `d²` (symmetric ⇒ ≤
N(N+1)/2; rank ≤ d shrinks it further). Taking "Gram" literally
**undercounts** — `d² = 25` is the dimension of the *full, unconstrained*
2-point operator space `V ⊗ V ≅ End V` (all `d²` components), which a Gram
matrix does not have. `gramMatrixEntries` happened to read `d²` only because
it counts *entries*, not DOF.

So "Gram" is a **view promoted to identity** (CLAUDE.md failure mode): the
whole `Gram*` file family names the correction after one incidental reading.
The mechanism is the **generic degree-2 / 2-point operator-space**
normalization — exactly the leg `GramD2Mechanism` already used (`tensorDim`,
not Gram DOF). The insight validates that leg and exposes the name as legacy
(inherited from `GramStructural`/`GramSelfEnergy`).

**Consequence — two d-facts were conflated under "Gram":**
- **denominator `d²`** = ambient 2-point operator-space dimension (`/d²`),
  independent of the object's rank;
- **rank ≤ d** = the object's *effective content* (cf. the "rank-1 effective
  trace", `refined_trace` weight=1 at k=1) — a numerator/`α²`-side fact.

Separating them gives the clean form `α²/d² = (α/d)²` — the squared
per-state-dimension coupling, a generic second-order self-energy with **no
Gram-matrix machinery**. This brings the remaining premise closer to
tautological (an `O(α²)` correction *is* a 2-point object).

**Still open after the reframe**: why normalization is by the *full* `d²`
(ambient) rather than a rank-reduced count. Reading (a) "divide by the
dimension of the space the 2-point object lives in" ⇒ `d²` correct, Gram-rank
irrelevant (cleaner, and consistent with the `tensorDim` grounding); reading
(b) a genuinely rank-specific structure ⇒ re-examine. Evidence favors (a);
not yet a theorem (reframe/hypothesis, not formalized — premature
formalization would be fudge).

## Genuine negative result — the `1/d`-per-cup-factor rule is NOT derivable from the current cup infrastructure (2026-06-08)

Tried to promote `cup_graduation_denom k := d^(k+1)`
(`RefinedCupLadderDerivation` §1) from a *definition* to a derivation. It does
not close with what exists, and here is precisely why (so a future session
doesn't re-attempt the dead end):

- The existing cup product `cup 5 a b : Cochain 5 a → Cochain 5 b →
  Cochain 5 (a+b)` (`Cohomology/Cup/Core`) is **Bool / F₂-valued**. It carries
  **no `1/d` normalisation** — the `d^(k+1)` denominator is *added* by the
  `cup_graduation_denom` definition, not produced by the cup operation.
- `CupRingTrace.lean` confirms this by its own results: the elementary
  cup-ring functionals on `H*(Δ⁴; F₂)` give small integers (`F₁=F₂=4`,
  `F₃=80`, `F₄=240`, `F₅=120`) — none carries a `1/d` grading; the file's own
  gap analysis says the `1/d` spectral structure "isn't a small Δ⁴ count".
- Therefore deriving "each cup factor carries `1/d`" requires a **ℚ-coefficient
  *normalised* cup product** (cochains weighted by `1/d` per layer, à la a
  normalised bar/AW coproduct) — infrastructure that **does not exist** in the
  repo. Building it is the real multi-session task; asserting the rule from the
  Bool cup would be a posit dressed as a theorem (declined, §5.4 / CLAUDE.md
  "premature formalization = fudge").

So the `/d²` mechanism stands on its **solid leg** — `tensorDim d d = d²` =
`dim End V`, the 2-point operator-space dimension (real math, no cup
normalisation needed). The cup-graduation leg is a *consistency check*, not an
independent derivation, until a normalised cup product exists. The two legs
"converging" (`mechanisms_converge`) is genuine but one leg is definitional.

## External anchor (deep-research, 2026-06-08)

- **No standard-QFT precedent for normalising a self-energy by `d² = dim End V`
  / the square of the state-space dimension.** A two-point self-energy is
  standardly `Σ(p)` via Schwinger–Dyson `G⁻¹ = C⁻¹ − Σ`, with no `1/d²` factor.
- The superficially-similar **`1/N²` of matrix/tensor models is the *genus*
  (topological) expansion** — `1/N²` per handle (arXiv:2207.05520,
  hep-lat/9305007), a *different mechanism* from "normalise by `dim End V`".
  So the resemblance is coincidental in origin.
- Consequence: the `α²/d²` form has **no external grounding to borrow**; the
  "open, mechanism-identified-but-not-forced" verdict is the externally honest
  one. The solid content is internal: `dim End V = d²` is a real, DRLT-native
  fact; the *physical identification* of the Gram self-energy with that
  operator space is the (genuinely interpretive) open premise.

## What would fully close it

A theorem identifying the Gram self-energy functional *as* the `k=1`
self-pairing cup term (promoting `CupRingTrace`/`SelfPairingTrace` from a
bottom-up test to a forcing derivation that the self-energy IS the 2-fold
cup self-pairing). Then `correction = α²/d²` is fully atomic and the Gram
`modeling-form` DoF closes entirely.

A second, smaller sub-item (separate): replace the observed-α on the RHS
of `gram_correction_e9` with a 213-internal cubic-root iterate, and bound
the residual 27×10⁻⁹ (next-order Dyson tail).

## Anchors

- `lean/E213/Lib/Physics/AlphaEM/GramCubicReduction.lean` — the reduction (PURE)
- `lean/E213/Lib/Physics/AlphaEM/GramStructural.lean` — cubic anchor + "what remains"
- `lean/E213/Lib/Physics/AlphaEM/Augmented.lean` § GramSelfEnergy — the three d² readings
- `lean/E213/Lib/Physics/AlphaEM/CupRingTrace.lean` — the bottom-up test
- `DEGREES_OF_FREEDOM_LEDGER.md` Layer 3 — the DoF accounting
</content>
