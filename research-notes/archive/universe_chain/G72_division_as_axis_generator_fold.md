# G72: Division as the orthogonal-axis-generator fold

## User insight (2026-05-09)

> "P(x) = (2x+1)/(x+1)
>      = ((2x+1),(x+1))  -- Q213식 표기이자 두 직교축의 표현
>      = ((x+(x+1)),(x+1))
>      = ((x.succfolditer(x.succfold()), x.succfold()))"
>
> "P(x)에서 나누기 연산 자체도 fold여야 하잖아... 근데 이 렌즈에서는
> 다른종류의 fold인거지... 이게 나누기가 이질적인 이유인가봄
> 직교의 생성자 자체이기 때문에"

The division `/` in P(x) is itself a fold (since all lenses are
folds, proven), but a **DIFFERENT KIND of fold** — the
**orthogonal-axis-generator fold**.  This is why division feels
heterogeneous: it doesn't operate WITHIN a structure but
**creates a new structure** by establishing orthogonal axes.

## The fold hierarchy

Folds split into TWO categorical levels:

### Level 0: Within-axis folds (closed)

These operate on Nat213 → Nat213 → Nat213 and stay within Nat213:

| Fold | Recursion | Closed? |
|---|---|---|
| `succ` | atomic generator | yes (single arg) |
| `add` (= +) | succ-iteration on first arg | yes |
| `mul` (= ·) | add-iteration on first arg | yes |

These can be **iterated indefinitely** within Nat213 without
escaping.  Each is a catamorphism on Nat213's `one|succ` structure.

### Level 1: Axis-generating folds (escape)

These take Nat213² and produce a NEW structure (escaping Nat213):

| Fold | Maps to | Construction |
|---|---|---|
| `-` (subtraction) | ℤ | additive-diagonal quotient of Nat213² |
| `/` (division) | ℚ_+ | multiplicative-diagonal quotient of Nat213² |

These are the **orthogonal-axis generators** (G62 framework):
- `-` generates the additive orthogonal axis (= ℤ)
- `/` generates the multiplicative orthogonal axis (= ℚ_+)

They CANNOT stay within Nat213 because the inputs (a, b) with
a ≤ b have no Nat213 result for `a - b` (Nat213 has no zero/
negative), and similarly for `a / b` when a ∤ b.

## Why this matters: the heterogeneity of /

User's observation "나누기가 이질적인 이유 = 직교의 생성자 자체이기 때문" is precise:

- Within-axis folds (+, ·): apply WITHIN an existing structure
- Axis-generating folds (-, /): CONSTRUCT new structures
- These are at DIFFERENT categorical levels

So `/` is not "just another fold" — it's the fold that **brings
orthogonality into existence**.  Same for `-`.

## Möbius P decomposition revisited

`P(x) = (2x+1)/(x+1)` decomposes as:

```
P(x) = (numerator, denominator) ────────/─────→  ℚ_+
        ▲                                ▲
        │                                │
        │ (2x+1, x+1)              axis-generator fold (Level 1)
        │
        ├── 2x+1 = x + (x+1) ←── within-axis fold (add, Level 0)
        │            ▲
        │            │
        │            └── (x+1) = succ x ←── atomic fold (Level 0)
        │
        └── x+1 = succ x ←── atomic fold (Level 0)
```

So P(x) involves ALL THREE LEVELS:
- Level 0 (atomic): `succ` (= x+1)
- Level 0 (closed): `add` (= 2x+1 via two succ-applications)
- Level 1 (axis-gen): `/` (= the final division)

Möbius P is the **complete fold tower** in a single expression.

## User's pseudocode in Lean-ish form

```lean
-- Atomic fold
succ : Nat213 → Nat213
succ x = Nat213.succ x

-- Closed iteration: "+x" iterating succ x times
def succIter (n : Nat213) : Nat213 → Nat213
  | one    => Nat213.succ n
  | succ k => Nat213.succ (succIter n k)
-- This is essentially Nat213.add

-- Escape fold: requires extension to ℚ_+
-- def divFold : Nat213 → Nat213 → ℚ_+ := ...
```

## Connection to atomicity (G70)

The fold hierarchy aligns with the lens-fractal atomicity:

| Layer | Fold type | Atomicity role |
|---|---|---|
| Raw atoms (a, b) | structural binary | NT = 2 |
| Raw slash | within-axis fold | 1 op |
| Raw signature | full | NS = 3 |
| Nat213.succ | atomic fold | structural |
| Nat213.add (= +) | within-axis fold | level 0 |
| Nat213.mul (= ·) | within-axis fold | level 0 |
| ℤ (Nat213² / add-diag) | axis-generator: `-` | level 1 |
| ℚ_+ (Nat213² / mult-diag) | axis-generator: `/` | level 1 |

The (NS, NT, d) atomicity at constructor level is preserved across
all layers; the FOLD operates at structurally distinct levels
(0 = within-axis, 1 = axis-generating).

## Why ℚ ≅ ℤ at the (Nat213, Nat213) level

User's earlier observation: "정수도 (ℕ, ℕ), 유리수도 (ℕ, ℕ)" —
both ℤ and ℚ are quotients of Nat213².  They differ only in WHICH
axis-generator fold is applied:

```
Nat213² ──── - (additive quotient) ────→ ℤ
       ──── / (multiplicative quotient) → ℚ_+
       ──── (no quotient) ──────────────→ Nat213² (the ortho-pair itself)
```

The same orthogonal-pair structure, viewed through different
axis-generator folds, gives different output algebras.

## Lean ∅-axiom witnesses (existing + connection)

Already proved:
- `Nat213.add` closed (Core.lean) — within-axis fold
- `Nat213.mul` closed (Core.lean) — within-axis fold
- `no_absorbing_element` — Nat213 has no zero (preventing direct sub/div)
- `npairToInt` (Theory/Tower/NatPairToInt.lean) — / additive case
- `ntripleToZ2` (Theory/Tower/NatTripleToZ2.lean) — 3-axis Eisenstein

This note primarily synthesizes the categorical hierarchy; minor
new Lean theorems may follow.

## Conclusion

**Division `/` is heterogeneous because it's at the ORTHOGONAL-
AXIS-GENERATOR level, not the within-axis level**.  All folds are
catamorphisms, but they operate at structurally different levels:

- Level 0 folds (+, ·, succ): closed in Nat213
- Level 1 folds (-, /): escape into orthogonal extensions

User's intuition: validated and structurally precise.

## See also

- `lean/E213/Theory/Nat213/Core.lean` — closed folds
- `lean/E213/Theory/Tower/NatPairToInt.lean` — `-` axis-generator
- `research-notes/G62` — orthogonal-axis framework
- `research-notes/G65–G71` — Nat213/lens chain
