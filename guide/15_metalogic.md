# 15 — Metalogic: R1–R4 & Falsifiability

**Tier:** T0
**Status:** Closed; mechanically enforced via typeclasses + hooks.
**Lean:** `Meta/SelfRecognising.lean`,
`Meta/Tactic/{DeriveConjugationCodomain, VerifyConjugation}.lean`,
`Meta/AxiomMinimality.lean`, `Meta/AxiomMinimalityCapstone.lean`.

## Best current statement

213 has its own metalogic — a self-checking layer that verifies whether
candidate codomains (algebras hosting the Lens) satisfy the four
substrate conditions R1–R4 (see Ch. 01).

### R1–R4 typeclass hierarchy

```
R12Codomain : binary combine + commutativity
R3Codomain  : extends R12; non-vanishing (no zero divisors)
R4Codomain  : extends R3; swap involution distributes over combine
```

Each level is a Lean typeclass; instance checking is decidable at
compile time. The `verify_conjugation` / `derive_conjugation_codomain`
tactics in `Meta/Tactic/` synthesize an instance or fail — making
R1–R4 a **mechanical falsifier of candidates**.

### Verified instances

- `Int`, `Int[√D]` (quadratic extensions): full R4Codomain.
- `Bool` with AND or OR lens: R12, fails R3 (idempotent).
- `Bool` with XOR lens: R12 + R3, **fails R4** — formally proven.

XOR-fails-R4 is the first concrete demonstration that an alternative
substrate candidate is rejected by 213's own metalogic.

## Falsifiability discipline (`seed/AXIOM/08_falsifiability.md`)

Seven explicit observational falsifiers:

1. Neutrino ordering (JUNO ~2030)
2. θ_QCD bracket (next-gen nEDM, 2027–30)
3. 4th generation existence (LHC ongoing)
4. PMNS angle deviations
5. Cabibbo λ refinement (LHCb / Belle II)
6. Proton mass refinement
7. Magic numbers (any deviation → discard)

Any prediction violated outside its bracket → entire framework
discarded. Binding — not "the section is revised". Mechanically
enforced by `tools/kernel_regress.sh` and `tools/FORBIDDEN.md`, which
forbid `sorry`, `axiom`, `import Mathlib`, `open Classical`,
`native_decide` in `lean/E213/Term/*.lean`.

## 213 sharpening

- Instead of informal falsification, **typed falsification**
  (`#verify_r4` as a tactic).
- Instead of external axiom-counting, **internal minimality**
  (`AxiomMinimality.lean`).
- Instead of trust in proof checking, **decide-only Kernel** with no
  Mathlib surface area to hide non-constructive steps.

## Open / next

- Tighten `AxiomMinimality.lean` to a single theorem: "the four Raw
  clauses are pairwise independent and jointly minimal".
- Catalog of failed-R4 alternative codomain candidates — currently
  only Bool/XOR. Goal: rule out finite fields, etc.
- Decide whether `Meta/SelfRecognising` should subsume R1–R4
  typeclass inheritance — currently parallel.

## Sources

- `seed/AXIOM/01_residue.md`, `seed/AXIOM/08_falsifiability.md`.
- `lean/E213/Meta/SelfRecognising.lean`.
- `lean/E213/Meta/Tactic/{DeriveConjugationCodomain,
  VerifyConjugation}.lean`.
- `lean/E213/Meta/AxiomMinimality.lean`,
  `Meta/AxiomMinimalityCapstone.lean`.
- `tools/FORBIDDEN.md`, `tools/kernel_regress.sh`.
