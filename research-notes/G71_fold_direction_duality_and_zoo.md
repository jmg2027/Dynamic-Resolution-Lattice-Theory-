# G71: Fold-direction duality + multi-level fold zoo

## User intuition (2026-05-09)

> "2방향이 fold연산인건가, 3은 fold연산의 결과인거고
>  아님 반대인가, 반대라고 해도 말이 되는거같기도 하고 ㅋㅋ
>  2x+1이 fold이기도 하고 x+1이 fold이기도 하고 /가 fold이기도 하고…
>  뭐 다른 종류의 fold이면서 각도에 따라 교대로 그 종류들이 달라질
>  수도 있는거고… 어질어질하게 어렵네 진짜"

Two questions:
1. Is **2** the fold-direction and **3** the result?  Or reversed?
2. Multiple things appear to be folds: `2x+1`, `x+1`, `/`, ...
   Are they "different kinds" interchanging by perspective?

## Answer 1: NS-NT duality is genuine — both readings work

The lens framework Raw → Nat213 has:
- **Source side (Raw, 3 ctors)**: NS = 3
- **Target side (Nat213, 2 ctors)**: NT = 2
- **Bridge (the lens)**: catamorphism = fold

Reading A — "2 is fold-direction":
- The 2 atoms in Raw (a, b) define the **input direction**
- Fold operates on this binary axis to produce 3-component output
- (NT-direction → NS-result)

Reading B — "3 is fold-direction":
- The 3 Raw constructors define the **fold structure** (slash recursion)
- Fold operates on this ternary signature to produce 2-component output
- (NS-direction → NT-result)

Both readings are valid because:
- A lens is an **arrow Raw → Nat213** that connects NS=3 source and
  NT=2 target
- "Direction" depends on which side you call "input"
- The fold ITSELF is the bridge — it's neither 2 nor 3 alone, but
  the **mapping** that connects them

This is the **NS↔NT duality**: the two sides of the lens are
interchangeable depending on perspective.  The fold IS the
bidirectional bridge.

## Answer 2: Yes, multiple folds — at different fractal levels

Each level of the fractal has its own catamorphism (= "fold"):

| Level | Inductive structure | Fold operation | Atomicity |
|---|---|---|---|
| Raw | a, b, slash | `Raw.fold ba bb combine` | 3 ctors = NS |
| Nat213 | one, succ | `Nat213.add` (= succ-iter) | 2 ctors = NT |
| Int213 | ofNat, negSucc | Int recursion | 2 ctors |
| ℤ[i] (Gaussian) | re, im (CD-doubled) | CD recursion | 2 ctors per layer |
| Möbius P-orbit | matrix iter | linear recurrence | trace=3, det=1 |

So **"fold" is a level-indexed family** of catamorphisms, each on
its own type.  User's examples:
- **`/` (slash)**: Raw's binary fold-primitive
- **`x+1` (succ)**: Nat213's increment-fold
- **`2x+1`**: Möbius P numerator (= [[2,1]] linear-fold)
- **addition**: Nat213.add = succ-iteration on first arg
- **(a, b) ~ (c, d)**: NPair-level diagonal-quotient fold

Each fold is "different" but unified by being a **catamorphism**
on some inductive type.

## The Möbius P encoding

Möbius P matrix `[[2, 1], [1, 1]]` packages all atomicity
constants:

| Entry / Invariant | Value | Atomicity ID |
|---|---|---|
| Top-left entry | 2 | NT |
| Sum of all entries | 5 | d |
| Trace (= 2+1) | 3 | NS |
| Discriminant (= tr² - 4·det = 9 - 4) | 5 | d |
| Determinant | 1 | identity (unit) |
| Eigenvalues | φ², 1/φ² | golden-ratio dyad |

So (NS, NT, d) = (3, 2, 5) is structurally encoded in P:
- NT in matrix entry
- NS in trace
- d in entry-sum AND discriminant (consistent)

The user's "2x+1이 fold, x+1이 fold" — both are linear functions
appearing as the rows of P:
- Row 1: `(2, 1)` → `2x + 1·y` (= numerator of P)
- Row 2: `(1, 1)` → `1x + 1·y` (= denominator of P)

So:
- **Row 1 (NT-direction)**: `2x+1` = NT-coefficient * x + 1
- **Row 2 (unit-direction)**: `x+1` = identity * x + 1

The two rows of P split as **(NT-loaded, unit-loaded)** — packaging
the (NS, NT, d) atomicity into a 2×2 matrix.

## "Different kinds of folds, alternating by perspective"

User's intuition crystallizes as:

> Different inductive types have different catamorphisms.  But the
> ATOMICITY pattern (NS=3, NT=2, d=5) reappears at every level,
> with NS/NT roles potentially swapped depending on which side you
> consider "input" vs "output".

Examples of role-swapping:
- Raw → Nat213: NS=3 is source, NT=2 is target
- Nat213 → Raw (embedding via natToRaw): would invert roles
- ℤ → ℤ[i] (CD doubling): NT=2 is the doubling factor, NS=3 is...
- Möbius P iteration: trace=3 is the iteration "weight", entry 2
  is the "atom factor"

The duality is structural: every Lens has 2 sides + 1 bridge,
giving the 2/3 split in some assignment.

## Lean ∅-axiom witnesses

Already exist:
- `Theory/Raw/Mobius.lean` — Möbius P trace, det, disc, eigenvalues
- `Theory/Nat213/AtomicityCorrespondence.lean` — NS=3, NT=2, d=5
- `Theory/Nat213/Lenses.lean` — lens infrastructure with 3-tuple

This note primarily synthesizes; minimal new Lean (single helper).

## "어질어질하게 어렵네" — why it's dizzying

The recursive nature of fold-zoo is genuinely vertiginous:
- Each level has its own fold
- Each level encodes (NS, NT, d) somehow
- Roles swap between levels
- The whole fractal has self-similar structure

This dizziness is a **feature, not a bug** — it's the signature of
a true fractal.  Resolution-dependence + role-swapping + recursive
self-similarity = fractal.

## See also

- `lean/E213/Theory/Raw/Mobius.lean` — Möbius P
- `lean/E213/Theory/Nat213/AtomicityCorrespondence.lean` — NS/NT/d
- `research-notes/G57_213_mobius_signature.md` — original Möbius
- `research-notes/G65–G70` — Nat213/lens framework chain
