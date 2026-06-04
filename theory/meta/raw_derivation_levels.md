# "Raw-derived" at Three Levels — Logical / Structural / Operational

**Status**: Closed (conceptual taxonomy from Raw-derivation three-level taxonomy;
empirical evidence from Expr-level callgraph, Raw-depth BFS, namespace-shape + recursor inventory).

## Overview

The phrase **"everything in DRLT is derived from Raw"** has three
distinct technical meanings.  Each is **TRUE or FALSE on a
different basis**.  Conflation muddies the reading.

|  Level | Meaning | Truth |
|---|---|---|
| (α) Logical | Every theorem closes under Lean kernel + 4-clause Raw axiom + 213 axiom suite | **TRUE** |
| (β) Structural-content | Mathematical content of DRLT derivable from 4-clause Raw alone | **TRUE** |
| (γ) Operational / definitional | Every theorem's proof body + type signature reduces to Raw atoms via Expr edges | **FALSE in general** |

**(γ) being false doesn't undermine (α) or (β).**  DRLT's
architecture is: **Raw-derived mathematical content layered on
generic Lean carrier infrastructure**.  The mathematics is
Raw-derived; the carriers (Nat, Bool, Int, Fin, ...) are not.

## Source

- **Primary**: `research-notes/archive/metascan/G104_raw_derivation_three_levels.md`
- **Empirical evidence**: Expr-level callgraph (Expr callgraph BFS), Raw-depth BFS (Raw-depth
  density), namespace-shape + recursor inventory (per-namespace shape + recursor inventory),
  `tools/ast_typesig_scan.py`, `tools/ast_callgraph_scan.py`

## The three levels

### (α) Logical derivability — TRUE

Every E213 theorem closes under Lean's kernel + the 4-clause Raw
axiom set + the 213 axiom suite.  **No external axiom.**

Verified by:
- `#print axioms` on every cited core lemma → "does not depend on
  any axioms" or `≤ {propext, Quot.sound}` for the sealed-by-design
  set
- Lean-core dep-purity audit: 0 non-sealed DIRTY citations
- Parallel branch closure of all DIRTY-cited remnants (N5/N6
  centralisation)

This is the **logical** version of the claim.  True and verified
by axiom-tracking, not by Expr-pattern analysis.

DRLT is **PURE-bounded on Lean 4 core**.  There is no axiomatic
escape hatch.

### (β) Structural-content derivability — TRUE

The mathematical **content** of DRLT — specifically the
inevitability chain:

```
Raw → (NS, NT, d) = (3, 2, 5) → 6-theorem
```

including the alive predicate (now Clause-4 recursive per
parallel branch's `AliveDerivation.alive_iff_clause4_alive`),
**is provably derivable from the 4-clause Raw axiom alone**.

The atomicity / Pell unit invariant / ZOmega^× = C_6 / dual filling
χ-sum chain (parallel branch's Raw-native emergence audit + diophantine completeness
commits) constructs the corpus's headline numbers from Raw
without invoking external content.

This is the **structural-mathematical** version of the claim.
True, but verified by the parallel substantive branch's
content work, not by meta-scans on this branch.

See:
- `theory/physics/foundations/atomic_constants.md` (C2 closure)
- `theory/math/universe_chain.md` (atomicity → CRT)
- `theory/math/cayley_dickson/algebra_tower.md` (algebra-tower
  asymptote φ matching Möbius signature)

### (γ) Operational / definitional reduction — FALSE in general

**Claim**: every theorem's PROOF BODY and TYPE SIGNATURE Expr
should transitively reduce to references to Raw atoms (`raw.ctor`,
`raw.elim`, etc.) via forward Expr edges within finite depth.

**Empirically false.**  Expr-level callgraph (body refs) + Raw-depth BFS §1 + Raw-derivation three-level taxonomy §2
(type-sig refs) show only **~15%** of E213 declarations reach a
Raw atom via Expr-level forward edges within finite depth.

The rest use **carrier types** that are generic Lean infrastructure:
- `Cochain n k := Fin (binom n k) → Bool` (Bool-valued indicator)
- `binom : Nat → Nat → Nat` (Nat arithmetic, not Raw arithmetic)
- `Cut : Real213.Cut` (built on Nat/Int)
- `Fin n`, `Bool`, `Nat`, `Int`, `List` — Lean stdlib carriers

These carriers are defined in **Nat/Bool/Int/Fin** terms, **not in
Raw-construction terms**.  At the operational Expr level, ~85% of
E213 theorems route through generic Lean carriers.

## Why the three-level distinction matters

### For framework defense

When asked "is DRLT really derived from Raw?", the answer needs
all three levels:

1. *Yes* (α): no external axiom outside the Raw + 213 axiom set
2. *Yes* (β): the mathematical content (atomicity, Möbius, gauge
   emergence, α_em precision) is derivable from Raw axiom alone
3. *No* (γ): proof terms and type signatures use generic Lean
   carriers, not Raw atoms

Conflating (α/β) with (γ) leads to either:
- Over-claiming: "everything is *literally* Raw at every level" — false
- Under-claiming: "DRLT depends on Lean's Nat/Bool" — misleading;
  it depends on (α) Lean kernel + (β) Raw axiom; carriers are
  implementation choices, not axiom load

### For abstraction work

The L1 LeibnizAlgLift family (6-layer byte-identical confirmation,
implicit-lemma extraction) shows that abstraction candidates should be sought at the
**Expr-level structural** layer, not the **logical/content** layer.
The 6 layers of confirmation isolate **proof-skeleton** patterns
that are independent of mathematical content.

This refines what counts as a "good abstraction": one where the
Expr-level structure repeats while the content varies, not just
"both prove similar-looking theorems".

### For carriers vs content

DRLT carriers (Nat, Bool, etc.) are **interchangeable** in
principle — different Lean-internal representations of the same
213-content would not change (α) or (β).  Carriers are an
implementation layer below the Raw-derived content.

The cleanest formulation: **DRLT = Raw-derived mathematics layered
on generic Lean carriers**.

## Empirical methodology

The three-level distinction was extracted by:

1. **(α) verification**: `tools/audit_axioms.py` + per-theorem
   `#print axioms`.  Outcome: 0 non-sealed DIRTY.
2. **(β) verification**: parallel substantive branch's content
   theorems (Raw-native emergence audit audit, diophantine completeness, atomicity
   chain).  Outcome: Raw → headline numbers chain closes.
3. **(γ) measurement**: `tools/ast_typesig_scan.py` +
   `tools/ast_callgraph_scan.py` BFS from each E213 declaration
   toward Raw atoms.  Outcome: 15% reach Raw within finite depth;
   85% bottom out at carrier types.

The 15% figure depends on BFS depth limit; raising it doesn't
qualitatively change the conclusion because the carrier types are
**self-loops** at the Lean-stdlib boundary, not paths toward Raw.

## Architecture implication

DRLT's architecture is **two-layer**:

```
┌─────────────────────────────────────────┐
│ Layer 2: Raw-derived 213 content        │
│   (atomicity, Möbius, gauge, α_em, ...) │
│   Closes under (β)                      │
├─────────────────────────────────────────┤
│ Layer 1: Generic Lean carriers          │
│   (Nat, Bool, Int, Fin, List, ...)      │
│   Provides operational realization      │
│   Doesn't close under (β); doesn't need to │
└─────────────────────────────────────────┘
```

The (α) logical guarantee covers **both layers**: Lean kernel
sees them as one consistent system.  But the **content claim** is
about Layer 2; Layer 1 is implementation.

## How to verify

```bash
# (α) — axiom audit
python3 tools/audit_axioms.py

# (β) — verify substantive content chains
cd lean
lake build E213.Lib.Physics.Foundations.AtomicConstants
lake build E213.Lib.Math.Foundations.UniverseChain
lake build E213.Lib.Math.Algebra.CayleyDickson.Tower

# (γ) — empirical Expr-level reduction measurement
python3 tools/ast_typesig_scan.py --report-only
python3 tools/ast_callgraph_scan.py --report-only --target-raw
```

Expected:
- (α) audit reports 0 non-sealed DIRTY
- (β) builds clean
- (γ) ~15% reach Raw via Expr edges within finite BFS depth

## Citation guidance

When making a "derived from Raw" claim, **always specify the level**:

```
-- ✅ precise
"Every E213 theorem is logically (α) derived from Raw + 213 axiom set."
"The atomicity chain is structurally (β) derived from the 4-clause Raw axiom."

-- ❌ ambiguous
"Everything in DRLT is derived from Raw."
```

For the conceptual distinction itself, cite this chapter:
`theory/meta/raw_derivation_levels.md`.
