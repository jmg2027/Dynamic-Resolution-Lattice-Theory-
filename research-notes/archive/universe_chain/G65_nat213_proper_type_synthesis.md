# G65: Proper Nat213 type + nested-pair CD-recursion synthesis

## User insights (2026-05-09 latest)

1. "Raw에 어떤 렌즈를 가져다가 정의해서 만들어도 직교축을 추가하지
   않으면 0 혹은 음수를 정의할수가 없을거야"
2. "현재 Nat213은 lean4의 Nat이나 현대수학의 ℕ과는 다른거임"
3. "Nat213을 제대로 정의해서 성질 규명은 해야겠다"
4. "0을 더하거나 곱하면 다 0이 되어버림 — 임의의 두 수 연산하면 삐구"
5. "(N, N) → ℤ도 ℚ도 — 본질적으로 같은거구만 213에서는"
6. "(((a),(b)),((c),(d))) = (a*1 + b*(-1)) + (c*1 + d*(-1))*i"
   nested-pair recursion → ℤ[i] / Gaussian integer

## Findings

### F1. Current "Nat213" is NOT a 213-native type

Inspection of `lean/E213/Term/Tactic/Nat213.lean`:
```
namespace E213.Tactic.Nat213
```
The file contains ∅-axiom **helper theorems** for Lean's built-in
`Nat` (replacing propext-leaking core lemmas).  No new type is
defined.  Name is misleading — should be `NatHelpers` or similar.

**There is no proper 213-native ℕ type yet.**  This is a real gap.

### F2. Lens insight — orthogonal axis required for negatives/0

Raw.fold takes `(base_a, base_b, combine)`.  With base values both
in ℕ_+ (positive naturals) and combine = `(· + ·)`, the image is
**always positive**.  Producing 0 or negative requires:
- base_a or base_b = 0 (or negative — which needs ℤ already), OR
- combine = `(· - ·)` (which needs negation), OR
- Different lens entirely (base values in ℂ, ℍ, ...)

Without orthogonal-axis material in the codomain, fold cannot
produce 0 or negatives.  The orthogonal axis is **necessary
infrastructure** for sign / zero.

### F3. Same syntax, multiple semantics — (ℕ, ℕ) is ambiguous

| Pair (a, b) | Quotient | Result |
|---|---|---|
| (a, b) | additive: a + d = b + c | ℤ (a - b) |
| (a, b) | multiplicative: a · d = b · c | ℚ_+ (a/b) |
| (a, b) | direct (no quotient) | ℕ² lattice |

Until you commit to a "comma operation" (= quotient relation), the
pair `(a, b)` carries multiple potential meanings.

User observation: "정수도 (ℕ, ℕ), 유리수도 (ℕ, ℕ) — 본질적으로 같다"
— **the (ℕ, ℕ) container is universal; the meaning depends on the
projection.**

### F4. (1, 1), (1, 1) = "0/0" interpretation

In Cayley-Dickson nested form:
```
((1, 1), (1, 1)) = (1 - 1) + (1 - 1)·i = 0 + 0i = 0 ∈ ℤ[i]
```

This represents `0 ∈ ℂ` (= ℤ[i] zero).  Could equally be read as:
- "0/0" (multiplicative undefined)
- "0 + 0i" (additive: zero of ℂ)
- diagonal-of-diagonal collapse (geometric)

All three readings agree at the element-level; the ambiguity is
**which structure-mod we're in**.

### F5. Nested-pair = Cayley-Dickson tower (user proposal)

User's recursive structure:
```
Level 0:  a                                          ∈ ℕ
Level 1:  (a, b)              = a·1 + b·(-1)         ∈ ℤ
Level 2:  ((a,b), (c,d))      = (a-b) + (c-d)·i      ∈ ℤ[i]
Level 3:  (((a,b),(c,d)), ((e,f),(g,h)))
                              = ... + ... ·j         ∈ Lipschitz
```

The COEFFICIENT pattern at each level:
- L1 coef: -1 (real involution)
- L2 coef: i (i² = -1)
- L3 coef: j (j² = -1, jk = i, ...)

This is **literally Cayley-Dickson** in nested-pair notation, where:
- Each nesting depth = one orthogonal axis added
- Each level's "comma" interprets its level's CD-coefficient

So the user's notation **unifies** orthogonal-axis-tower (G62/G63)
with CD-tower (the standard ℝ→ℂ→ℍ→𝕆 chain).

### F6. 0's pathology — operations destabilize

Once 0 is in ℤ:
- `0 + n = n`: identity (OK)
- `0 · n = 0`: **absorption** (every product with 0 collapses)
- `0 - 0 = 0`, `n - n = 0`: cancellation produces 0
- Division `n / 0` undefined: **partial operation introduced**

In ℕ_+ (without 0):
- Addition: closed (m + n ≥ 1)
- Multiplication: closed (m · n ≥ 1)
- Subtraction: NOT closed (1 - 2 undefined within ℕ_+)
- All operations totally defined within their closure

So **ℕ_+ has cleaner operation algebra than ℕ-with-0**.  The
"absorption" pathology is introduced by extension to ℤ.

## Proposed Nat213 type

Following user's principle "Raw의 모습에서 자연스레 나오는 방향":

```lean
/-- 213-native ℕ: positive naturals derivable from Raw atom counting.
    Raw has at least 1 atom (a or b), so its count is ≥ 1.  This is
    NOT the same as Lean's `Nat` (which has 0).  -/
inductive Nat213 : Type
  | one  : Nat213
  | succ : Nat213 → Nat213
  deriving DecidableEq

namespace Nat213

/-- Embed into Lean Nat. -/
def toNat : Nat213 → Nat
  | .one => 1
  | .succ n => n.toNat + 1

/-- Addition: closed on Nat213. -/
def add : Nat213 → Nat213 → Nat213
  | .one, n => .succ n
  | .succ m, n => .succ (add m n)

/-- Multiplication: closed on Nat213. -/
def mul : Nat213 → Nat213 → Nat213
  | .one, n => n
  | .succ m, n => add n (mul m n)

end Nat213
```

This is a constructive Peano ℕ_+ — "1, 2, 3, ..." with no 0.

**Properties this gives**:
- Addition closed (no 0 absorption)
- Multiplication closed (1 · n = n is identity, no 0 absorption)
- Subtraction NOT defined within Nat213 (1 - 1 doesn't exist here)
- Total order: Nat213.le (1 is minimum, no maximum)

**Properties this loses (vs Lean Nat)**:
- 0 element absent (intentional)
- 0-based fold base impossible (must use 1 as base)
- Some arithmetic identities reformulated (`n - n = 0` doesn't make
  sense without quotient)

## Where 0 enters

**0 is NOT in Nat213**.  It enters only through:

| Path | Construction |
|---|---|
| Diagonal quotient | (Nat213 × Nat213) / additive-diag → ℤ |
| Multiplicative quotient | (Nat213 × Nat213) / mult-diag → ℚ_+ |
| Cayley-Dickson level-N | Nested pairs with antipode coefficients |
| Group identity | Forced by group axioms when extending |

In every case, 0 = **artifact of structural extension**, never
derivable from Raw or Nat213 directly.

## Operations: 2-axis vs 3-axis vs k-axis

User hint: "2축 방향과 3축 방향이 각각 다른 연산이라거나"

If we have multiple parallel "addition-like" operations (one per
axis pair), we get a richer structure:

| k axes | Operations | Resulting algebra |
|---|---|---|
| 1 (just Nat213) | + (closed), · (closed) | semiring ℕ_+ |
| 2 (Nat213²) | +, "diag-axis" projection | ℤ via subtraction quotient |
| 3 (Nat213³) | +, "ω-axis" projection | ℤ[ω] via Eisenstein quotient |
| 2 (CD form) | +, ·, "i-axis" | ℂ via Gaussian / CD |

So "operation" at each level ↔ "axis quotient" at that level.

## Proposed next steps (in order)

1. **Define Nat213 type** (Peano ℕ_+ inductive) in
   `lean/E213/Theory/Nat213/Core.lean`
2. **Operations**: addition, multiplication, partial subtraction
3. **Connection to Lean Nat**: `toNat`, `ofNatPos` (for n ≥ 1)
4. **Connection to Raw**: `Raw.atomCount : Raw → Nat213` (= count of
   atoms, always ≥ 1 since Raw has at least one)
5. **(Nat213 × Nat213) → ℤ projection**: redo `NatPairToInt.lean`
   with Nat213 base, see how 0-emergence becomes explicit
6. **Nested-pair CD construction**: define inductively
   ```
   def NestedPair : Nat → Type
     | 0 => Nat213
     | n+1 => NestedPair n × NestedPair n
   ```
   With interpretation function to ℂ / ℍ / 𝕆 / ...

## See also

- `lean/E213/Term/Tactic/Nat213.lean` — current (misnamed) helpers
- `lean/E213/Theory/Raw.lean` — Raw API (atoms always ≥ 1)
- `lean/E213/Theory/Tower/NatPairToInt.lean` — current orth-axis projection
- `research-notes/G62-G64` — prior synthesis
