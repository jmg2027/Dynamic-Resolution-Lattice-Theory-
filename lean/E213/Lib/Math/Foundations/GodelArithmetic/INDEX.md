# GodelArithmetic — Gödel marathon (Phase 1)

Concrete-arithmetic complement to the abstract Lawvere-form
`Lib/Math/UniverseChain/{Lawvere, Godel}.lean`.

## Phase 1 (this commit)

| File                                  | Theorems |
|---------------------------------------|----------|
| `AbstractProp.lean`                   | `godel_inconsistency` |
| `IncompletenessVsConsistency.lean`    | `incompleteness_or_inconsistency`, `real_godel_capstone` |
| `Formula.lean`                        | `depth_*`, `leafCount_*`, `encode_*` |
| `Capstone.lean`                       | `phase1_capstone` |

**Status**: 14/14 ∅-axiom (kernel-verified).

## Phase 2 (future)

  1. **Injectivity** of `Formula.encode` — proper pairing function.
  2. **Substitution** `subst : Formula → Nat → Nat → Formula`.
  3. **Diagonal-construction** `diag : (Nat → Formula) → Formula`.
  4. **Diagonal lemma proof** for the concrete Formula.
  5. **Explicit Gödel sentence** via the diagonal applied to ¬Prov.
  6. **Concrete incompleteness theorem** combining the above.

## Relationship to existing modules

  * `Lib/Math/UniverseChain/Lawvere.lean` — abstract Lawvere
    fixed-point theorem (∅-axiom).  Mathematical engine.
  * `Lib/Math/UniverseChain/Godel.lean` — Bool-form abstract Gödel
    inconsistency.
  * `Lib/Math/Infinity/Cantor.lean` — `cantor_general`,
    surjection-blocker.
  * **This sub-tree** — Prop-form abstract Gödel + concrete-syntax
    scaffold for landing the abstract result on real syntax.

## Honest ledger

**Proven (Phase 1)**:

  * Abstract: total Prop-valued provability + diagonal ⇒ inconsistent.
  * Trade-off: consistent + Gödel sentence ⇒ incomplete.
  * Concrete syntax with structural ops + Gödel-numbering shape.

**Stated, not proven (Phase 2)**:

  * Diagonal lemma for concrete arithmetic — the heart of Gödel I.
  * Construction of an explicit Gödel sentence for `Formula`.

**Out of scope**:

  * Gödel's *second* incompleteness theorem.
  * Full ω-incompleteness.
  * Rigorous arithmetisation of Robinson Q.

## ∅-axiom verification

```
lake build E213.Lib.Math.Foundations.GodelArithmetic.Capstone
```

per-theorem `#print axioms` empty (14/14).
