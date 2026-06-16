# Standard-common-sense contamination audit (math / foundations / lens / meta)

**Origin:** multi-agent re-examination pass — "find where standard mathematical
common sense has been silently imported as if it were 213-native truth"
(physics out of scope).  Method: grep the tell-tale smell phrases ("the real",
"underlying", "from outside", "oracle", "the value", "canonical form", "lowest
terms", "approaches/reaches", "the continuum", "foundation of", equivalence/iso/
homomorphism) across `theory/`, `seed/AXIOM/`, and Lean docstrings; keep only the
hits whose framing actually imports an exterior/ontology (not the ones already
tagged or negated in place).

## Verdict: corpus is unusually disciplined

The overwhelming majority of smell-phrase hits are *already* dissolved in place
("not imposed from outside", "reached by none", "in ZFC … by contrast").
Swept and found genuinely clean: `theory/lens/` (equivalence/iso/homomorphism
correctly one Lens-arrow); the completeness/limit essays (every limit tagged
"reached by none / the cut already computes it"); `phi_self_similarity.md`
("approaches but never reaches" = the residue unit `+1`, not a deified limit);
`seed/AXIOM/` (§5.1/§5.4 used as the guard, not violated).

## Fixed this pass — the SignedCut "oracle / value-layer" substrate metaphor

The one real cluster, and it mattered because **Lean is source of truth** so the
contaminated docstring propagates against the canonical narrative ("the tuple is
the number", `slot_arithmetic.md` §1).

- `SignedCut/Core/Core.lean` — "the represented value is `pos − neg` at the
  **underlying real**" / "the value is recovered … at the **oracle
  interpretation**" → **Substrate metaphor** + **Quotient-promoted-to-ontology**:
  posits a value-layer *beneath* the pair.  **Fixed**: the pair *is* the signed
  object (difference-Lens on a directed cut-pair, `06_lens_readings.md` §6.7);
  `pos − neg` is one *flattening* readout, not recovery of an exterior value
  (none exists, §5.1).
- `SignedCut/Core/Equivalence.lean` — "213-native paradigm: **the standard
  ℤ-from-ℕ construction**" (Stereotype-match) + "At the **value layer (oracle)**,
  representatives are interchangeable" (Substrate) + a dated PR-provenance line
  with residual Korean.  **Fixed**: the difference-Lens readout, of which the
  classical Grothendieck quotient is the *flattened image*; interchangeability
  **is** the structural relation among pairs, no exterior value-layer where they
  "secretly coincide"; provenance line removed (English-only, no process narration).

## Remaining minor candidates (low priority — not yet fixed)

1. `theory/math/geometry/topology.md:31` — "list-finite **at the resolution
   `N_U`**" reads `N_U` as *the* resolution before the file self-corrects 12
   lines later ("not a privileged resolution cap").  Cosmetic ordering smell
   (Universe-constant framing, transient): lead with the parametric statement
   ("list-finite at every finite fractal level `n`; `configCount n` bounds the
   cover") so the privileged reading is never asserted even in passing.
   Confidence low; self-corrected in-file.
2. The DyadicSearch "oracle" files (`ConsistentOracle`, `UnitConsistentOracles`,
   `OracleContinuity`) use "oracle" in the legitimate **decision-oracle** sense
   (a query function for bisection), **not** a substrate metaphor — *not*
   contamination; left as-is.  Recorded here so a future grep on "oracle" does
   not re-flag them.

## For future passes

The grep-for-smell-phrases method works but the signal is sparse (the corpus is
clean) — the high-yield target is **Lean docstrings that drifted from the
narrative tier**, since the org discipline keeps `theory/` clean but docstrings
are edited per-PR and can lag.  Re-run focused on `lean/E213/**` docstrings
against their `theory/` mirror when a number-system or quotient sub-tree changes.

## Round 2 — Lean-docstring-vs-narrative drift sweep

Ran the high-yield target above (Lean docstrings under `Lib/Math`, `Lens`,
`Theory`, `Meta` vs their `theory/` mirrors).  **Verdict: held up — one
low-severity register drift, fixed; everything else clean.**

- **Fixed**: `Real213/PresentationDependence.lean:12` — "the **underlying real**
  (the decidable cut) is invariant under a common rescaling" made *the real* the
  subject with "underlying" (substrate register), where line 30 of the *same
  file* and the canonical mirror (`tower_native_completeness.md:204`) make **the
  cut** the rescaling-invariant subject.  Rewrote to "the **cut** (the decidable
  real) is invariant …".  One-clause edit; the file is otherwise rigorously
  presentation-relative.
- **Confirmed clean** (smell-phrase hits that are *not* contamination):
  `GaugeDiagonal.lean:57` ("in ZFC … equivalence class" — tagged as the flattened
  Lens-image); `IntFoldForms.lean` ("adjoined ∞" — the §6.9 compactification, anti-
  stratum); `Cardinality.lean:20` / `Theory/Raw/Core.lean:12` ("not a substrate" /
  "quotient emulation" as a Lean encoding-cost); `RatioLensFounding.lean:17`
  ("lowest terms" as the unimodular *theorem* `det P = 1`); `ChebyshevLower.lean:380`
  ("true value log₂e" — immediately qualified as the ln-base shadow, anti-
  deification); all DyadicSearch decision-"oracle" files (round-1 pre-cleared).

Net across both rounds: the corpus is disciplined; docstring drift is real but
rare (round 1: SignedCut oracle/value-layer cluster; round 2: one word in one
file).  The per-PR-lag risk is genuine — keep re-running this sweep when a
number-system / quotient / completeness sub-tree changes.
