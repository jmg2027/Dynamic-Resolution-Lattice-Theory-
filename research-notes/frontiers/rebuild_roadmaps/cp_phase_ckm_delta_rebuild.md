# CP phase δ / CKM rebuild (post-deletion of the typed-ratio fudges)

**What was deleted & the bogus mechanism.**  `CPViolation.lean` carried a typed
CP-phase ratio with no derivation, deleted in `26c86991e`:

```lean
def delta_approx_num : Nat := 176
def delta_approx_den : Nat := 147
theorem delta_approx_value :
    delta_approx_num = 176 ∧ delta_approx_den = 147 := by decide      -- 176=176 ∧ 147=147
```

`delta_approx_value` is the tautology `176 = 176 ∧ 147 = 147` — the numbers `176`,
`147` were *typed in*, then "proven" to equal themselves. It derives nothing about
δ. The companion fudge `ckm_delta_3sig` reached the observed value only by a
hand-added `+31` — an exterior dialer (`seed/AXIOM/05_no_exterior.md` §5.1),
exactly the move the framework forbids. Both are number-matching dressed as
derivation.

**The genuine content.**  The CP phase δ is the **Jarlskog-invariant phase** of
the CKM matrix — the single rephasing-invariant whose nonvanishing (`J ≠ 0`)
*is* CP violation. A real derivation produces δ (or `J`) from a structure
(a complex/cohomological `i`, a mixing geometry), as a *computed bracket excluding
nearby values*, not a typed ratio. The unitarity-triangle apex `z = ρ̄ + iη̄` and
`J = Im(...)` are the genuine targets.

**The 213-native obstruction.**  CP violation needs a genuine **complex phase** —
an `i` with `i² = −1` arising structurally, plus a geometry whose `Im` part is
nonzero. The fudges skipped this by typing the answer. 213 has the genuine
ingredients, already PURE, and they are *coherent* with each other:
- **the cohomological `i`:** `SignedStarC4` proves the signed Hodge star `J = ⋆`
  on the `d−1 = 4` simplex has order 4 (`⋆² = −I`, `⋆⁴ = I`, `⋆² ≠ I`), i.e.
  `J` generates `C₄ = ℤ[i]^×` — a *derived* `i`, not posited.
  `Mixing/CPPhaseHodgeBridge.cp_c4_is_signed_hodge_group` upgrades the old
  hand-written list `[(1,0),(0,1),(-1,0),(0,-1)]` to the genuine `{J⁰,J¹,J²,J³}`,
  giving `δ = 360/4 = 90°` from the *actual* `⋆`-operator. (Honest tier `◑`: a
  `decide` bundle; `J`-as-`hodgeStar` is a docstring identification.)
- **the φ²-coherent apex:** `Mixing/JarlskogApex` records the apex as a single
  golden object — magnitude `1/φ²`, phase `π/φ²` — with the Jarlskog numerics
  matching at +1.4% (`J = 3.12×10⁻⁵` vs observed `3.08×10⁻⁵`), and `φ²` is
  DRLT-atomic (`φ² + 1/φ² = NS = 3`, `GoldenRatio.golden_ratio_atomic`). The file
  is honest: it **labels `R_u = 1/φ²` a CANDIDATE** — exact φ-identities are PURE,
  but *why* the apex modulus is exactly `1/φ²` is "not yet a forcing theorem".
- **the internal mechanism:** `Mixing/ApexCPMechanism` derives the apex
  `z = r·e^{iπr}` from the self-reference map `M = [[c,1],[1,1]]` (§5.6) — the
  frozen eigenvalue gives `r = 1/φ²` (real, no phase), the dynamic reading gives
  the central involution `M⁵ ≡ −I = e^{iπ}` (the phase `π`). CP violation exists
  *iff* the half-period element is `−1` — a genuine falsifiable core, no external
  flavour model.

**Staged plan (citing genuine seams).**

- **Stage 1 — δ from the `C₄` structure, stated as the genuine 90° + φ²-twist.**
  Keep `cp_c4_is_signed_hodge_group` (the `⋆`-derived `δ = 90°`) and
  `ApexCPMechanism` (`δ = π/φ²` from `M⁵ = −I`) as the two faces, both PURE, both
  honest about the surviving physics readings ("this `⋆`-phase IS the CKM phase",
  "`J ∝ Im`") — flagged as readings, NOT proven identities.
- **Stage 2 — a computed bracket excluding nearby values.**  Replace any typed
  ratio with a *bracket*: prove `δ`'s 213-value (`π/φ²` ≈ 137°, or the unitarity-
  triangle angle the data prefer) lies in an interval that **excludes** the nearby
  competitor values, using the Fibonacci convergents of `1/φ²`
  (`F₃/F₅ = 2/5`, `F₅/F₇ = 5/13`, …) as the narrowing sequence — the modulus/bracket
  is the computable operand (the limit never is). This is the "compute a bracket,
  exclude neighbours" discipline, the antithesis of `176 = 176`.
- **Stage 3 — force the apex modulus.**  The genuine open kernel: turn
  `R_u = 1/φ²` from CANDIDATE into a forcing theorem — *why* `1/φ²` and not another
  φ-power. `JarlskogApex` names this precisely as the remaining gap; `φ²` being
  atomic (`φ²+1/φ²=3`) is the handle.
- **Stage 4 — Jarlskog `J` as the falsifier.**  State `J = η·(...)` with `η =
  (1/φ²)·sin(π/φ²)` as a measurable prediction in a window (observed
  `J ≈ 3.08×10⁻⁵`), with the `J ∝ Im` reading flagged. No `+31`, no hand-tuned
  offset — if the window misses, the candidate is falsified, not patched.

**Honest scope.**  No typed δ ratio (`176/147` or any literal). No additive
fudge (`+31` = exterior dialer, forbidden, §5.1). The cohomological `i` (`C₄`,
order 4, 90°) is *genuinely derived*; the apex modulus `1/φ²` is a *strong
candidate, not forced*; the identifications "`⋆`-phase = CKM phase" and "`J ∝ Im`"
are *readings*, not theorems. δ may be presented only as a computed bracket
excluding neighbours, with these scope flags intact.

**Cross-references.**
- `lean/E213/Lib/Physics/Mixing/CPPhaseHodgeBridge.lean` (`cp_c4_is_signed_hodge_group`, the genuine `C₄`)
- `lean/E213/Lib/Physics/Mixing/JarlskogApex.lean` (`R_u = 1/φ²` CANDIDATE, φ²-coherence)
- `lean/E213/Lib/Physics/Mixing/ApexCPMechanism.lean` (`z = r·e^{iπr}` from `M⁵ = −I`, internal)
- `lean/E213/Lib/Math/Cohomology/Hodge/SignedStarC4.lean` (`⋆² = −I`, the cohomological `i`)
- `lean/E213/Lib/Physics/Foundations/GoldenRatio.lean` (`golden_ratio_atomic`, `φ²+1/φ²=3`)
- `seed/AXIOM/05_no_exterior.md` §5.1 + §5.6 (no exterior dialer; the `M`/`π/φ²` self-reference)
- `research-notes/frontiers/ckm_rho_eta_apex.md` (the apex-factor frontier)
