import E213.Math.Real213

/-! Spec-as-code entry point for `E213.Math` — Real213 + topical kit.

Importing this single module pulls in the **entire 213-native
real-number library** (`Math/Real213.lean` umbrella) plus the
remaining math top-level files (PatternCatalog, ResolutionLimit, …)
when they're imported separately.

## Sub-trees

- **`Real213`** — full 213-native real-analysis library (108 files).
  Type foundation + Cut algebra + Differentiation + Integration +
  Flux-MVT + Cauchy + Series + Dyadic search + ODE.

- **Per-chapter sub-umbrellas** (still available for consumers
  needing only a slice; each is a strict subset of Real213.lean):
  `Math/Foundation`, `Math/CutOps`, `Math/Cauchy`, `Math/Series`,
  `Math/Continuity`, `Math/Analysis`, `Math/Analysis213`,
  `Math/Generic`.

- **Other top-level Math files** (independent of Real213):
  `Math/PatternCatalog*`, `Math/ResolutionLimit`, `Math/AddMod213`,
  `Math/EncodePair213`, etc.  Importing this umbrella does NOT pull
  these in — consumers must import them directly.

## Status

∅-axiom standard on the production critical path.  Pre-M5 research
scaffold orphans (referencing session-27-deleted function-eq
theorems) have been removed.
-/
