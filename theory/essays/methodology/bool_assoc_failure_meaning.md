# Why cutSum associativity fails at the Bool level for b ≥ 3

`cutSum`'s search granularity is hardcoded to factor-2, so it reflects only NT of the
(NS, NT) = (3, 2) atom and drops NS.  The diagnosis is not a problem "outside" the
framework but that *the cutSum implementation under-realizes 213's atomic commitment*.

## Arithmetic diagnosis

The condition for `cutSum (constCut a b) (constCut c b) m k = true`:

```
∃ m1 ∈ [0, 2m]:  a · 2k ≤ b · m1  ∧  c · 2k ≤ b · (2m − m1)
⇔  ⌈2ka/b⌉ + ⌈2kc/b⌉ ≤ 2m
```

The condition for `constCut (a+c) b m k = true`:

```
(a+c) · k ≤ b · m  ⇔  ⌈2k(a+c)/b⌉ ≤ 2m
```

The difference between the two conditions is the **ceiling super-additivity gap**:

```
⌈X/b⌉ + ⌈Y/b⌉  ≥  ⌈(X+Y)/b⌉    (over-shoot of at most (b-1)/b, twice)
```

For the gap to be 0, `2k/b` must be an integer.  Factor-2 doubling absorbs the
denominator of b = 2 but cannot absorb the denominator of b = 3.

## The real boundary is the (3, 2) atomic basis

| b | 213 status | Basis |
|---|---|---|
| 1 | trivial | integer |
| 2 | NT atom | `Physics/Foundations/AtomicConstantsParametricFullIff.lean` `c2b_full_iff` |
| 3 | NS atom | same theorem — (m, n) = (3, 2) or (2, 3) uniqueness |
| 5 | unique alive atomic of (3, 2) | `Theory/Atomicity/Five.lean` `atomic_iff_five` |
| 4, 6, 8, 9, 12, ... | multiplicative composite of {2, 3} | product of the two atoms above |
| 7, 11, ... | additive Lens-readout from (3, 2) possible | Bezout via gcd(2,3) = 1 |

**5 is not a new atom but derived**.  `atomic_iff_five` proves exactly that
"5 = the uniquely alive atomic decomposition of (3, 2)": 5 = 2·1 + 3·1.  d = 5 = NS + NT
is *a readout of (3, 2)*.

`Lib/Math/Foundations/ResolutionLimit.lean` `N_U_eq_d_pow_dsq`: N_U = 5²⁵ — automatic
since 5 is forced from (3, 2).

`Lib/Math/NumberSystems/Padic/ZpSqrtD.lean` `ZpSqrtD p`: works at any prime `p`
(p = 5, 7, 11, ...).  The framework already holds every prime within itself.

`Lib/Math/Cohomology/Bipartite.lean`: the bipartite (3-side, 2-side) structure of
K_{3,2}^{(c=2)} generates every observable as a cup-ring.

`Lib/Physics/AlphaEM/Capstone.lean` `unified_single_sum_form`: α_em is derived from
(3, 2, 5) alone — 0.2 ppb CODATA agreement.

All these theorems form a Lean-proven chain of *(3, 2) → every real decision*.  An
"outside" the framework is rejected by §5.1 (`seed/AXIOM/05_no_exterior.md`).

## The cutSum diagnosis (corrected)

The problem is not b ≥ 3 but:

**`cutSum`'s factor-2 hardcode read only NT of (3, 2) and dropped NS**.

A correct cutSum must reflect both of (3, 2):

  · search granularity is `lcm`-aware, not factor-2
  · for the denominators `b₁, b₂` of the two cuts, search range = `lcm(b₁, b₂) · m`
  · in the {2, 3}-multiplicative monoid it closes automatically (lcm is in the same monoid)
  · the ceiling gap becomes exactly 0 on the native class, recovering associativity

Or, more deeply: the resolution should be determined by which Lens application the cut came
from (Lens-determined granularity).  A hardcoded factor-2 is the implicit assumption that
*every cut is treated as an NT-Lens output*.

## Effect on equality

It is no accident that the equivalence definitions enumerated in the previous essay
(`cutEq`, `ZpSeqEquiv`, `signedEq`, ...) are already well-defined at any
denominator / any prime — it is a direct expression of the fact that *the framework holds
every real decision from (3, 2)*.

`is_integer : cutEq cut (constCut a 1)` (`IntValidCut.lean`) and
`is_half : cutEq cut (constCut a 2)` (`HalfValidCut.lean`) can also be consolidated into a
more general wrapper:

```
is_native : cutEq cut (constCut a b) ∧ b ∈ ⟨2, 3⟩  (multiplicative monoid)
```

In this wrapper, associativity closes together with a (3, 2)-aware implementation of
cutSum.

## Closure of the follow-up work

1. **`cutSumN N` parametric definition** — `Lib/Math/NumberSystems/Real213/Sum/CutSumN.lean` (6 PURE).  Lifts the factor-2 hardcode to a parametric N.  `cutSumN_same_denom`: at any `N > 0`, `a, c`, `cutSumN N (constCut a N) (constCut c N) ≡ constCut (a+c) N` bidirectional.

2. **`cutSumN_mixed_denom`** — `Sum/CutSumNMixed.lean` (3 PURE).  Cross-denominator closure: for `b₁·q₁ = N`, `b₂·q₂ = N`,
   `cutSumN N (constCut a b₁) (constCut c b₂) ≡ constCut (a·q₁ + c·q₂) N`.  Every pair of divisors b of N closes algebraically.  Example: `cutSumN 6 (1/2) (1/3) ≡ 5/6` (`cutSumN_six_half_third`).

3. **`ThirdValidCut` (b = 3)** — `Lib/Math/NumberSystems/Real213/ValidCut/ThirdValidCut.lean` (15 PURE).  IntValidCut/HalfValidCut pattern; based on `cutSumN 3`.  `cutSumN_3_2_1_at_1_1` decide-verifies that the CutSumAssocB3 counterexample is true under `cutSumN 3`.

4. **`NValidCut N` parametric — unified closure for every natural number N** — `Lib/Math/NumberSystems/Real213/ValidCut/NValidCut.lean` (14 PURE).  `ValidCutN N` structure (cut + represents + is_at_denom), `addN N hN`, `cutSumN_assoc_valid N hN`, `cutSumN_comm_valid N hN`, `nvalidcut_all_naturals_capstone`.  No per-N proof needed — closes in one shot at any N ≥ 1.  Smoke: associativity verified at N = 5, 7, 11 (`fifth_assoc_1_2_1`, `seventh_assoc_2_3_5`, `eleventh_assoc_1_4_6`).

## 5 and every natural number: layered closure

| Layer | Closure | Lean |
|---|---|---|
| Self-algebra (single N) | any N ≥ 1 | `cutSumN_same_denom N` + `NValidCut N` |
| Mixed (b₁, b₂ | N) | N a common multiple of b₁, b₂ | `cutSumN_mixed_denom` |
| 213-native composite | N ∈ ⟨2, 3⟩^mult | b = 2, 3, 4, 6, 8, 9, 12, ... all cross-sums |
| Pure b = 5, 7, 11, ... | Self-closure ✓; cross-closure needs N = b·b' | NValidCut N |

**The place of 5**: `Theory/Atomicity/Five.lean atomic_iff_five` proves that
5 = 2·1 + 3·1 (alive atomic) — 5 is the unique atomic *by addition* from (3, 2).
cutSumN 5 closes as self-algebra; cutSumN 10 = cutSumN (2·5) gives the b ∈ {2, 5} pair
cross-closure.  7 = 2+2+3, 11 = 2+3+3+3, etc., follow the same pattern.

The real framework defect is cutSum's hardcode, not b ≥ 3 itself.  213 honors the (3, 2)
atomic commitment, and within it every real is decidable.  The `cutSumN N` parametric
framework fully realizes, within the framework, the algebraic closure of the NS·NT atom
**for every natural number**.
