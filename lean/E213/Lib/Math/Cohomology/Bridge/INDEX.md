# `Cohomology/Bridge/` — Cohomology external bridges

Bridge layer connecting 213 cohomology to Real213 / AlphaEM /
Paper1 chiral structure / Leibniz finding.  Anti-corruption layer
between cohomology results and external clusters.

## Files (9)

### To other Math clusters
  - `Real213Bridge.lean`           — to Real213 (cuts ↔ cohomology)
  - `CutExpFiniteTruncation.lean`  — `cutExp` finite truncation
                                     used in cohomology arithmetic
  - `CutLog.lean`                  — `cutLog` bridge

### To Physics
  - `AlphaEMBridge.lean`           — α_em ↔ cup-ring

### Closure / extension
  - `ClosureExtension.lean`        — closure-extension lemma
  - `TrivialCases.lean`            — trivial-case isolation

### Pair / Xor combinatorics
  - `XorPairCombine.lean`          — XOR-pair combinator

### History / external
  - `Paper1Chiral.lean`            — Paper1 chiral-structure bridge
  - `LeibnizFinding.lean`          — Leibniz finding writeup

## Bridge discipline (CLAUDE.md)

Per CLAUDE.md "Bridge.lean" pattern: this cluster is an
anti-corruption layer.  External vocabulary (Real213 cuts, α_em
constants, Paper1 chiral terms) stays inside the bridge;
results re-stated in 213-cohomology-native form.

## Where to add new files

  - Bridge to Math cluster X    → `<X>Bridge.lean`
  - Bridge to Physics cluster   → `<Physics>Bridge.lean`
  - Historical writeup          → `<paper>Chiral` / `<...>Finding`
