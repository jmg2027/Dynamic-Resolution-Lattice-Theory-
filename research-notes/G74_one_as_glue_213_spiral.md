# G74: 1 as the rotation axis — 213 spiral / 5-perspective manifold

## User insight (2026-05-09)

> "이게 정말 90도일까?  숫자부터 다르잖아 2,3으로.  직교면 얘네들이
>  어떻게 서로 힘을 받아가면서 올라가것어.  이 두종류 폴드를 연결
>  하는 애가 있는거야"
>
> "1이라면 어떨까. 1이 접착제인거임... 회전축인거임.  그래서 '어떤
>  관점'에선 2축으로 보였던게 3축으로 보이고 3축으로 보였던게 2축
>  으로 보인다.  그게 바로 2-3/3-2 나선이자 프랙탈 모양을 만드는
>  특별한 폴드"
>
> "2-1-3 얘들은 혼자서는 아무것도 못해... 셋중 하나만 있는건 불가능
>  — 나머지는 자동으로 나오거든.  이게 바로 213이 어질어질한 구조
>  인 본질적인 이유"
>
> "5가지의 관점으로 볼 수 있고... 어떤 5개의 점을 골라도 2,3으로
>  보이는 다양체"

## The breakthrough

NS=3 and NT=2 are NOT truly orthogonal in isolation — they're
coprime (gcd = 1).  If genuinely orthogonal, no interaction.  But
they DO interact — they "lift each other" through the third
structural element: **1 = the glue / rotation axis**.

## 1 as glue: where it appears

### In Möbius P matrix

`[[2, 1], [1, 1]]` decomposed:
- top-left: 2 = NT (binary axis)
- diagonal sum: 2+1 = 3 = NS = trace
- off-diagonal: (1, 1) = the GLUE (connects)
- determinant: 2·1 - 1·1 = 1 = rotation invariant
- sum of all entries: 2+1+1+1 = 5 = d

So Möbius P literally is `(NT, glue, glue, unit) = (2, 1, 1, 1)`.

### NS - NT = 1 (Nat213 difference)

Formalized in OneAsGlue.lean:
- ns_minus_nt_is_one: NS - NT = 1 (= glue is the difference)
- ns_is_succ_nt: NS = NT + 1 (glue elevates NT to NS)

So 3 = 2 + 1.  Glue ELEVATES NT to NS.

## Indissolubility of 2-1-3

| Have | Auto-derive |
|---|---|
| 2 (NT) + 1 (glue) | 3 (NS) = 2 + 1 |
| 3 (NS) + 1 (glue) | 2 (NT) = 3 - 1 |
| 2 + 3 (NT + NS) | 1 (glue) = 3 - 2 |

Any TWO determines the THIRD via arithmetic.  No subset stands
alone — genuinely 3-fold indissoluble.

## Lean ∅-axiom witnesses

In Theory/Nat213/OneAsGlue.lean (7 theorems):

| Theorem | Statement |
|---|---|
| mobius_entries_sum_to_d | 2+1+1+1 = 5 |
| one_is_det | det = 1 (rotation invariant) |
| off_diagonal_is_two_ones | 1+1 = 2 (twin glue) |
| indissoluble_decomposition | NS + NT = d |
| ns_minus_nt_is_one | NS - NT = 1 (glue = difference) |
| ns_is_succ_nt | NS = NT + 1 (glue elevates) |
| ns_nt_product | NS · NT = 6 (Eisenstein dim) |

All ∅-axiom.

## Why "어질어질"

Three sources:
1. Mutual constitution — 2, 1, 3 each define the others
2. Self-similarity — same pattern at every fractal level
3. Role-swapping — NS↔NT under 90° rotation, but rotation IS 1

User's insight: this dizziness is structural, not accidental.

## Physics connection (DRLT)

- NT=2 = temporal axes
- NS=3 = spatial axes
- 1 = Lorentz-style boost (rotation between space and time)
- d=5 = total spacetime dimensions

The glue 1 IS the boost generator.

## See also

- lean/E213/Lib/Math/Mobius213.lean
- lean/E213/Theory/Nat213/OneAsGlue.lean (NEW)
- research-notes/G70-G73 (prior chain)
