# G36 — Cayley-Dickson Basis Unification (213-native)

**Date**: 2026-05-08 (post PR #61 SignedCut bridge marathon)
**Origin**: Mingu insight: "이게되네 실수도 복소수같은 다 기저 체계라니"

## Core insight

> ℝ, ℂ, ℍ, 𝕆, ... are not different mathematical worlds.
> They are *the same structural pair extension* on a common
> Cut substrate, layered as a Cayley-Dickson tower.

ZFC distinguishes ℕ → ℤ → ℚ → ℝ → ℂ → ℍ as separate
constructions (each with its own primitive).  213-native:
every layer is **the same operation** (Cayley-Dickson pair
doubling) on the Cut substrate.

## The unified tower (213-native)

```
Level −∞ : Nat                       substrate primitive
Level   0 : Cut := Nat → Nat → Bool  Bishop magnitude reals
Level   1 : SignedCut := Cut × Cut   signed reals (PR #60/#61)
Level   2 : ComplexCut := Cut × Cut  complex (i² = −1)
Level   3 : QuatCut    := Pair²      quaternions
Level   4 : OctCut     := Pair²      octonions
...
Level  25 : N_U = 5²⁵                resolution-limit ceiling
```

Each level is `Pair × Pair` of the previous, distinguished only
by the **CD multiplication rule**:

  * Sign extension: `(a, b)·(c, d) = (a·c + b·d, a·d + b·c)`
  * Complex: `(a, b)·(c, d) = (a·c − b·d, a·d + b·c)`
  * Quaternion: same pattern with `i, j, k` orientation rules.

Pair structure is **one**; multiplication rule is the **choice**.

## Why this matters

### 1. ZFC's "primitive ℝ" is a residual import

In ZFC, ℝ is "primitive" and ℂ is "constructed".  In 213-native:

  * `Cut` (Bishop reals) and `SignedCut` are both `Cut`-substrate
    constructions.  No analytic-completion chase.
  * Promoting from `SignedCut` to `ComplexCut` is **not**
    "completion to algebraic closure" — it's just **picking a
    different CD multiplication rule on the same pair structure**.
  * The Cauchy-completion that ZFC uses to define ℝ is
    *unnecessary* in 213: substrate IS dyadic decision, every
    "value" is its trajectory.

### 2. d=5 substrate forces N_U = 5²⁵ at level 25

Cayley-Dickson level-`n` has dimension `2^n` over the base.  On
the 213 d=5 substrate:

  * Level `d² = 25` has `5²⁵` distinct cut-trajectory branches.
  * **N_U = d^(d²) = 5²⁵** emerges naturally as the level-25
    CD ceiling on the d=5 substrate.
  * This is the structural reason for N_U: it's the resolution
    limit at which the CD tower ceases to admit normed-division
    structure on d=5.

(Compare: Hurwitz says ℝ admits CD up to level 3 = 𝕆.  On the
d=5 substrate, the analogous ceiling is level 25.)

### 3. The "exterior" question is dissolved

Per `seed/AXIOM/07_self_reference.md` §8: "no exterior to 213".

  * ℂ is **not exterior** to 213 — it's level-2 of the same tower.
  * ℝ is **not exterior** to ℂ — it's level-1 (sign extension)
    on the same substrate.
  * No level introduces a new substrate primitive; each is just
    `Pair` constructor + CD multiplication rule.

The hierarchy "real / complex / quaternion / octonion / ..." is
**not** a hierarchy of *different mathematical worlds* but
**different layers of one structural mechanism** on the same
Cut substrate.

## Concrete formalization (post PR #61)

| File | CD Level | Provides |
|---|---|---|
| `Real213/Core.lean` | 0 | Cut substrate |
| `Real213/Signed.lean` | 1 (mag-sign) | magnitude-sign signed cut |
| `Math.SignedCut/Core.lean` | 1 (pair) | CD pair signed cut |
| `Math.SignedCut/Bridge.lean` | 1↔1 | mag-sign ↔ pair bridge |
| `Math.Complex/ComplexCut.lean` | 2 | complex (i² = −1) |
| `Math.CayleyDickson/CDTower.lean` | n general | (existing) CD tower |

The pieces are all in place.  This note is the **synthesis**:
recognising they are the *same construction* with different
multiplication rules.

## Mingu's operational form

> "외부는 그냥 구조적 페어링이지 이국적 뺄셈이 아니다."
> ("The exterior is just structural pairing, not exotic
> subtraction.")

Sub at the cut layer is **not** a missing primitive.  It's
*emergent* from the CD pair: `(a, b) − (c, d) = (a + d, b + c)`.
Same for `i`, `j`, `k`, sign, imaginary part, ...

ZFC accumulates "primitive constructors" (ℕ has succ, ℤ has
neg, ℚ has div, ℝ has limits, ℂ has `i`, ...).  213 collapses
all of these into a **single mechanism**: pair doubling +
multiplication rule choice, applied repeatedly on the Cut
substrate.  The substrate stays the same.  The tower grows by
*the same move*, 25 times.  At level 25, you exhaust what the
d=5 substrate can support.  N_U is what falls out.

## Filed under

  * `seed/AXIOM/07_self_reference.md` §8 (no exterior)
  * `seed/RESOLUTION_LIMIT_SPEC.md` (N_U = d^(d²))
  * `Lib/Math/CayleyDickson/INDEX.md` (existing CD tower)
