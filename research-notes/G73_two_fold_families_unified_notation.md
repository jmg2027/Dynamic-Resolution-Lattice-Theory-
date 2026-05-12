# G73: Two fold families + unified `(),` notation

## User insight (2026-05-09)

> "이러면 그냥 두종류 연산이 있는거네(두종류 fold)
>  +,* 족 / -,/ 족
>  구별할 필요도 없어야 지금처럼 Nat213, Int213,... 으로 표기해서
>  (a) / ((a), (b)) 이런식으로 표기해버리면, * 도 없어도 되고 - 도 없어도됨"
>
> "유리수도 안 만들어도됨, Int213이랑 똑같이 생겼잖어"
>
> "이 두종류 연산을 90도로 뒤집어서 생각해보면, 아까는 +족이었던
>  애가 /족이 되고, /족이었던 애가 +족이 된다 (직교축이 2축 3축
>  이니까)"
>
> "+족을 (), /족을 ',' 라고 해도 편할수도"

## The two-family taxonomy (G72 expanded)

ALL Nat213-related folds split into **exactly two families**:

| Family | Members | Behavior |
|---|---|---|
| **+-family** | succ, add (+), mul (·) | **within-axis closed** |
| **/-family** | sub (-), div (/) | **axis-generator (escape)** |

This is exhaustive for Nat213-relevant folds:
- All within-axis closed operations are derivable from succ
- All axis-generator escapes are derivable from /-family

## The unified notation: `()` and `,`

User's proposed notation:

```
Level 0:  (a)                                     = Nat213
Level 1:  ((a), (b))                             = ortho-pair (ℤ or ℚ_+)
Level 2:  (((a), (b)), ((c), (d)))               = nested ortho (ℤ[i], etc.)
Level n:  inductively wrapped
```

The semantics:
- **`()`** = +-family wrapper (within-axis combination)
- **`,`** = /-family separator (axis-generator)

So `((a), (b))` reads: "two ()-wrapped elements separated by a `,`".
The COMMA is the axis-generator fold; the PARENTHESES are within-
axis containers.

### Single-fold-family interpretation

Different LENS choices on the same `((a), (b))` give:
- **ℤ-lens**: subtractive quotient → `(a, b) ↦ a - b`
- **ℚ_+-lens**: divisive quotient → `(a, b) ↦ a / b`
- **No quotient**: keep as Nat213²

But the **NOTATION is the same** for all three.  The lens choice
disambiguates.

## Why ℚ doesn't need separate construction

User's "유리수도 안 만들어도됨, Int213이랑 똑같이 생겼잖어":

```
ℤ:    ((a), (b))     -- with subtractive quotient (a - b)
ℚ_+:  ((a), (b))     -- with divisive quotient   (a / b)
```

**Same syntactic structure.**  Only the lens (= the operation
applied at the outer `,`) differs.

This is the practical realization of "container is universal,
meaning is lens-dependent" (G65 F3).

## The 90° flip — NS-NT swap

User's "90도로 뒤집어서": rotating the perspective swaps the role
of +-family and /-family:

| Perspective A | Perspective B (90° rotated) |
|---|---|
| `()` = +-family | `()` = /-family |
| `,` = /-family | `,` = +-family |
| NS = 3 = "structure" axis | NT = 2 = "structure" axis |
| NT = 2 = "atom" axis | NS = 3 = "atom" axis |

Both perspectives are valid (G71's NS-NT duality formalized).  The
choice of perspective = choice of "which family is the BASE
operation".

So the same `((a), (b))` can be read as:
- ℤ-element (`+`-base, `,`-escape via subtraction) — Perspective A
- ℚ_+-element (`/`-base, `,`-escape via subtraction-of-something-
  else) — Perspective B (rotated)

## Compact notation candidates

User: "쓰기 편한 표기법 발명하든가 ㅋㅋ".  Candidates:

### Option 1: Bracket levels
```
Level 0:  ⟨a⟩                — 1-axis
Level 1:  ⟨a, b⟩             — 2-axis (= ((a), (b)) flattened)
Level 2:  ⟨⟨a, b⟩, ⟨c, d⟩⟩    — 4-axis (CD step 1)
Level 3:  ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, ⟨⟨e,f⟩,⟨g,h⟩⟩⟩   — 8-axis (CD step 2)
```

### Option 2: Index-prefixed
```
0[a]
1[a, b]
2[1[a,b], 1[c,d]]
```

### Option 3: Type-tagged
```
N a              — Nat213
Z (a, b)         — ℤ via subtractive
Q (a, b)         — ℚ_+ via divisive
ZI ((a,b),(c,d)) — Gaussian via nested
```

The "official" 213-native notation can be chosen later.  For now,
documents the idea.

## Connection to Cayley-Dickson

The `((a), (b))` notation IS Cayley-Dickson at notation level:
- Level 0: ℕ_+ (= Nat213)
- Level 1 (subtractive): ℤ
- Level 1 (divisive): ℚ_+
- Level 2 (subtractive): ℤ[i] = Gaussian (= "ortho pair of ℤ-pairs")
- Level 3 (subtractive): Lipschitz quaternions

Each level wraps the previous in `()` and joins via `,`.

So **CD-tower IS the nested-pair tower**, and the SAME notation
captures the entire algebra ladder.

## Lean formalization (this commit)

Demonstrates:
- ℤ via additive quotient: already `Theory/Tower/NatPairToInt.lean`
- ℚ_+ via multiplicative quotient: NEW `Theory/Tower/NatPairToQPos.lean`
- Both as quotients of `Nat213 × Nat213`
- Same syntactic form, different lens

## Conclusion

User's vision: **two fold families + nested-pair notation = sufficient
for the entire 213 algebra tower**.

- `+`-family = within-axis fold (closed, level 0)
- `/`-family = axis-generator fold (escape, level 1)
- `()` = within-axis wrapper
- `,` = axis-generator separator
- 90° rotation swaps +/- families (NS-NT duality)
- ℤ and ℚ_+ are SYNTACTICALLY identical (`((a), (b))`), only lens
  differs

This is the **structural minimalism** of 213: every operation
reduces to two families, every algebra reduces to nested pairs of
Nat213.

## See also

- `lean/E213/Theory/Nat213/Core.lean` — Nat213 + closed folds
- `lean/E213/Theory/Tower/NatPairToInt.lean` — ℤ via additive
- `lean/E213/Theory/Tower/NatPairToQPos.lean` — ℚ_+ via multiplicative (NEW)
- `research-notes/G62, G65, G70–G72` — prior synthesis chain
