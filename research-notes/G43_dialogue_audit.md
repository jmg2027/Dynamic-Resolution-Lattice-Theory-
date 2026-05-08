# G43 — Dialogue Audit: Provable vs Heuristic

**Date**: 2026-05-08 (post G42 / PR #70)
**Origin**: Mingu's request to formally verify Gemini dialogue.

## Audit verdict

| Claim | Status |
|---|---|
| Both axes saturate at index 25 | ✅ **Proven** |
| Both axes are "same dyadic engine" | ❌ **Imprecise** — vert 2-adic, horiz 5-adic |
| Bit precision saturates at 5²⁵ | ⚠️ **Partial** — distinguishable bounded, index unbounded |
| Pigeonhole forces repetition past N_U | ✅ **Proven** (under substrate lens) |
| Z/2 chirality oscillation post-sat | ⚠️ **Heuristic** — Z/2 proven, oscillation metaphor |
| Planck length from N_U | ❌ **Physics conjecture, not formalized** |
| ZMod cyclicity strategy | ✅ Sound technique |

## Rigorously proven (this PR)

### 1. Axis distinction — 2-adic vs 5-adic

```
levelDim (n+1) = 2 * levelDim n              -- vertical
fsmGradeStates (j+1) = fsmGradeStates j * 5  -- horizontal
levelDim 25 < fsmGradeStates 25              -- ceilings differ
```

Dialogue's "둘 다 동일 dyadic" is *imprecise*: same INDEX 25,
different BASES (2 vs 5).

### 2. Joint saturation

```
levelDim 25 = 33,554,432       (= 2²⁵)
fsmGradeStates 25 = 298,023,223,876,953,125  (= 5²⁵ = N_U)
```

### 3. Pigeonhole at N_U

`5²⁵ < 5²⁵ + 1` — past N_U queries force repetition on
finite-state substrate.

### 4. Four distinct quantities

`25 < 2²⁵ < 5²⁵` — CD level depth, bit-tower dim, N_U all
distinct, all rigorously bounded.

## Honest interpretation

The dialogue's "비트 정밀도 = 5²⁵" claim:
  * **Bit index** (Nat depth in `c m k`): **unbounded**.
  * **Distinguishable cut count** on d=5 substrate: `5²⁵`.

Two meanings.  Dialogue uses the second.  Both must be
distinguished to avoid confusion.

## Heuristic claims (not formalized)

  * **Chirality oscillation post-saturation**: Z/2 grading
    proven (G37); oscillation interpretation requires
    substrate-runtime model.
  * **Planck length / Heisenberg from N_U**: physics bridge,
    deferred per "수학으로 완결" directive.

## Modules (4 .lean + 1 capstone, all ∅-axiom)

  * `AxisDistinction.lean`
  * `PigeonholeFiniteState.lean`
  * `BitPrecision.lean`
  * `G43Capstone.lean`

## Filed under

  * G36-G42 (PRs #62-#70)
  * `seed/RESOLUTION_LIMIT_SPEC.md`
