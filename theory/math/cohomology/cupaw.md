# Cohomology — CupAW

**Status**: Partially closed.  21+ files including the Leibniz
family (Decomp + UniversalLift + AlgLift{Alpha, Beta}).

## Overview

Alexander-Whitney cup (homotopy-coherent variant): the non-strict
cup product satisfying **graded Leibniz** `δ(α ∪ β) = δα ∪ β ± α ∪ δβ`.
Used in Hodge index proofs + α_em cup-channel inventory.

The CupAW layer is where the **self-referential lex-cup Leibniz open conjecture** sits — the
∀(k, l) self-referential Leibniz rule (HANDOFF Part 2 §A).

## Lean source

- `lean/E213/Lib/Math/Cohomology/CupAW/` (21+ files)
- ∅-axiom PURE on production critical path

### Leibniz family (closed bidegrees + decomposition machinery)

| File | Role |
|---|---|
| `Leibniz.lean` | Base Leibniz statements |
| `LeibnizLex*.lean` | Lex-projection cup variants |
| `Leibniz21Final.lean`, `Leibniz22Final.lean`, `Leibniz4Mixed.lean` | Specific bidegree closures (2,1) (2,2) mixed-4 |
| `LeibnizAlgLift.lean` + `21Alpha`, `22`, `22Alpha` | Algebraic-lift variants of Leibniz (self-referential lex-cup Leibniz Phase decomposition) |
| `LeibnizAlgLiftAlpha.lean` | Alpha-side algebraic lift parametric in bidegree |
| `LeibnizAlgLiftBeta.lean` | Beta-side algebraic lift parametric in bidegree |
| `LeibnizDecomp.lean` | **Decomposition machinery** for splitting Leibniz proofs into α/β halves |
| `LeibnizUniversalLift.lean` | Universal-lift infrastructure for arbitrary bidegree |

The batch (Decomp + UniversalLift + AlgLift{Alpha, Beta})
represents **structural progress toward self-referential lex-cup Leibniz closure**.  The strategy:
decompose the ∀(k, l) Leibniz into α/β halves + universal lift across
the bidegree parameter; each half is closeable parametrically (per
LeibnizAlgLiftAlpha/Beta), and Universal lifts the bundle.

## Narrative

### What CupAW is

The strict cup (`Cohomology/Cup/`) satisfies anti-commutativity but
NOT graded Leibniz: `δ(α ⌣ β) ≠ δα ⌣ β ± α ⌣ δβ` in general
(per cup-Δ Lens mismatch Lens-mismatch).  Alexander-Whitney's homotopy-coherent
variant **does** satisfy graded Leibniz at each fixed bidegree —
but the proof must be done **per bidegree**, not uniformly.

### Closed bidegrees

| (k, l) | Status | File |
|---|---|---|
| (1, 1) | ✓ list-level + Fin-indexed (Δ⁴) | `LeibnizLexListLevel`, `LeibnizLexSelfRef` |
| (2, 1) | ✓ list-level + Fin-indexed (Δ³) | `LeibnizLexStructural`, `LeibnizLex21` |
| (2, 2) | ✓ partial | `Leibniz22Final` |
| (4, 1, 1) | ✓ universal | `LeibnizMid.leibniz_universal_4_1_1` |
| (4, 1, 2) | ✓ universal | `Leibniz4Mixed.leibniz_universal_4_1_2` |
| (4, 2, 1) | ✓ universal (sister to (4, 1, 2)) | `Leibniz4Mixed.leibniz_universal_4_2_1` |
| (4, 2, 2) | ✓ universal | `Leibniz4Mixed.leibniz_universal_4_2_2` |
| (5, 1, 1) | ✓ universal | `Leibniz.leibniz_universal_5_1_1` |
| (5, 1, 2) | ✓ universal (via bilinearity lift) | `Leibniz5_1_2.leibniz_universal_5_1_2` |
| (5, 1, 3) | ✓ universal (meta-strategy generalized) | `Leibniz5_1_3.leibniz_universal_5_1_3` |
| (5, 2, 1) | ✓ universal | `Leibniz21Final.leibniz_universal_5_2_1` |
| (5, 2, 2) | ✓ universal | `Leibniz22Final.leibniz_universal_5_2_2` |
| **(k, l) general** | **OPEN** | — |

### self-referential lex-cup Leibniz open conjecture — Phase decomposition

Per `research-notes/G86_self_referential_lex_cup_leibniz.md`
(currently top-level active), the ∀(k, l) general case has the form:

```
deltaList (k+l) (cupList k l α β) τ
  =  (cupList (k+1) l (deltaList α) β) τ
   ⊕ (cupList k (l+1) α (deltaList β)) τ
   ⊕ correction(α, β, τ)
```

where `correction = (cupList k l α β)(τ \ {τ[mid]})` is the
**self-referential face-removal**.

The algebraic-lift batch (Alpha/Beta/Decomp/UniversalLift)
sets up the *decomposition* machinery to attack this — split the
proof into:
- α-half: bidegree-parametric δα contribution
- β-half: bidegree-parametric δβ contribution
- universal lift: combine + handle the correction term

The self-referential lex-cup Leibniz conjecture remains **open** at the full ∀(k, l) level (per
HANDOFF Part 2 §A and `research-notes/G86_*.md`); the Decomp + Lift
infrastructure is structural pre-work toward closure.

## Connection

- `theory/math/cohomology/hodge_conjecture.md` — HodgeConjecture/ uses CupAW machinery for the Hodge index pairings
- `theory/math/cohomology/cup.md` — strict cup (CupAW's non-Leibniz cousin)
- `theory/physics/alpha_em/precision_derivation.md` — α_em uses cup-channel inventory built on CupAW
- `research-notes/G85_cup_delta_lens_mismatch.md` — Why strict cup fails Leibniz; CupAW is the resolution
- `research-notes/G86_self_referential_lex_cup_leibniz.md` — **OPEN** ∀(k, l) conjecture
- `research-notes/archive/metascan/G111_cohomology_deep_dive.md` — Tier-2 Cohomology deep dive

## Open frontier

**self-referential lex-cup Leibniz ∀(k, l) Cup-Leibniz general** is
the active frontier.  Decomposition machinery (Decomp +
UniversalLift + AlgLift{Alpha, Beta}) is in place; full closure
pending.

Per self-referential lex-cup Leibniz §3 (speculative): closure may unlock
- α_em 5.4×10⁻⁴ residual via cup-product origin (chiral cup ring catalog §C1)
- K_{3,2}^{(c=2)} bipartite cup-channel structure
- θ_QCD α⁴ suppression as depth-(d-1) self-reference iteration
