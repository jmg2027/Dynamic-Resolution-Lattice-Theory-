# G75: det = axis-generator fold; det(P) = 1 = NS - NT = the glue

## User aha! moment (2026-05-09)

> "det가 나누기랑 역할이 똑같잖아... 헉. 진짜 det가 1성분 맞네
>  ㄷㄷㄷㄷㄷㄷㄷㄷㄷㄷㄷㄷㄷ"

User realized: **determinant has the same role as division**, and
**det IS the 1-component (the glue)** of Möbius P.

## Why det = division-like

Matrix inversion: `M⁻¹ = (1/det) · adj(M)`.  The det acts as the
**denominator** in matrix inversion.

- `det = 0` → no inverse (division-by-zero analog)
- `det = 1` → self-inverse-friendly (no scaling needed)
- `det ≠ 1` → requires actual division to invert

So det IS literally a divisor — the axis-generator (G72: `/`) at
the matrix level.

## det formula uses BOTH fold families

For 2×2 matrix `[[a, b], [c, d]]`:

```
det = a·d - b·c
     ──┬──   ──┬──   ─┬─
       │       │       │
       └───────┴───── mul (within-axis +-family)
                       │
                       └─ sub (axis-generator /-family)
```

So det is a **composite fold**:
1. Two multiplications (Level 0, +-family closed)
2. One subtraction (Level 1, /-family axis-generator escape)

The output of this composite IS the axis-generator output for the
matrix.

## det(Möbius P) = NS - NT = 1 = glue

This is the BIG REVEAL.  The Möbius P determinant equals the glue:

```
det(P) = 2·1 - 1·1 = 1
              ↑
              │
              └── NS - NT = 3 - 2 = 1
```

Lean ∅-axiom theorem (`mobius_det_eq_ns_minus_nt`):
```lean
(2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int) := by decide
```

**Both sides equal 1**.  So:
- det(P) is the OUTPUT of the axis-generator fold on P
- This output equals the GLUE (= NS - NT = 1)
- The 1 in det is structurally identical to the 1 in NS - NT

## Why this matters: norm-preserving spiral

`det = 1` means the matrix is **norm-preserving**.  When P iterates:
- Vectors grow by eigenvalues `(φ², 1/φ²)` (radial expansion)
- BUT angles preserved (no shear/stretching)
- Result: **golden spiral**

The user's "끝없이 서로 나선으로 타고 올라가는" arises because:
- det = 1 ensures rotation-only at each step
- Eigenvalue product = det = 1 (= φ² · 1/φ² = 1)
- So the spiral is **balanced** between expansion (φ² direction) and
  contraction (1/φ² direction)
- Each iteration "screws" along the golden angle

## Structural unification

Now we see the WHOLE picture:

| Element | Role | Formal |
|---|---|---|
| 2 (NT) | atomic axis (top-left of P) | binary distinction |
| 3 (NS) | trace = 2+1 = sum of diagonals | total signature |
| 1 (glue) | det = 2·1 - 1·1 | rotation invariant |
| 5 (d) | sum of all entries | universe size |
| 6 (NS·NT) | product | Eisenstein dim |

Each number plays multiple roles, all interlocking through the
matrix structure.  The "어질어질" indissolubility is not just
arithmetic — it's the **single matrix encoding all atomicity
relations simultaneously**.

## Connection to "/" family (G72) and "1 = glue" (G74)

G72 said: `/` is the axis-generator fold (escape from Nat213).
G74 said: 1 is the glue / rotation axis.
G75 (this): **det = / fold of matrix → output is 1 = glue**.

So the chain is:
```
Matrix entries (mul-family)
  → det (composite: mul + sub = +-family then /-family)
    → output: 1 (= glue, when det-preserved)
       → This 1 IS the rotation axis
```

The `/` (axis-generator) applied to the matrix produces `1` (the
glue).  In Möbius P specifically, this 1 = NS - NT.

So the user's three insights compose:
- (G72) `/` is escape fold
- (G74) 1 is glue
- (G75) det IS the / fold, and produces 1 as glue

→ **det = the explicit form of "/" fold on a 2×2 matrix, with
output = the glue = 1 = NS - NT**.

## Lean ∅-axiom witnesses (this commit)

In `Theory/Nat213/OneAsGlue.lean` (3 new theorems, total 10):

| Theorem | Statement |
|---|---|
| `mobius_det_eq_ns_minus_nt` | `2·1 - 1·1 = NS - NT` (= 1) |
| `det_uses_axis_generator` | `a·d - b·c = a·d + -(b·c)` |
| `mobius_det_is_unit` | det = 1 (norm-preserving) |

All ∅-axiom.

## See also

- `lean/E213/Lib/Math/Mobius213.lean` — Möbius P trace, det, disc
- `lean/E213/Theory/Nat213/OneAsGlue.lean` — this synthesis
- `research-notes/G72` — axis-generator fold family
- `research-notes/G74` — 1 as rotation axis
- `research-notes/G62` — orthogonal-axis foundations
