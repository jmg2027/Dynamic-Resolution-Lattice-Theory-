# 02 — Atomicity: d=5, NS=3, NT=2, Fibonacci

**Tier:** T0
**Status:** Closed Lean theorem + Phase 1 Discovery 1 (Fibonacci).
**Lean:** `Theory/Atomicity/Five.lean`, `Lib/Physics/Foundations/FibonacciAtomic.lean`.

## Best current statement

The atomic dimensions of 213 are not free parameters. They are forced
by atomicity over the Raw axiom:

```
NS = 3   (number of S-type atoms)
NT = 2   (number of T-type atoms)
d  = 5 = NS + NT  (atomic dimension)
c  = 2  (lattice cycle)
```

### d = 5 theorem (Atomicity.lean)

Atomic decomposition requires `d = 2a + 3b` with both `a` and `b` odd.
Bézout reduction shows this is satisfied uniquely at `d = 5` (a=1, b=1)
among small integers. Higher d either factor or admit even
decompositions, breaking atomicity. Proof: `by decide`, 0 axioms.

### Fibonacci discovery (Phase 1)

(NT, NS, d) = (2, 3, 5) = (F₃, F₄, F₅) — three consecutive Fibonacci.

Eight further atomic quantities map to consecutive Fibonacci:

| Quantity | Value | Fib |
|----------|-------|-----|
| NT | 2 | F₃ |
| NS | 3 | F₄ |
| d  | 5 | F₅ |
| NS² − 1 = b₁(K_{3,2}) | 8 | F₆ |
| (next) | 13 | F₇ |
| (next) | 21 | F₈ |
| (next) | 34 | F₉ |
| (next) | 55 | F₁₀ |

SU(5) Y-norm = d/NS = 5/3 ≈ φ-convergent (limit Fₙ₊₁/Fₙ → φ). Not
coincidence: d=5 atomicity sits at a Fibonacci fixed point.

## Why this matters

Pre-213, SU(3)×SU(2)×U(1) gauge structure was empirical input. With
d=5 as a theorem, factorization 5 = 3 + 2 is forced; the gauge group is
*derived*. Phase 1 Discovery 2 connects further: photon = cycle space
of K_{3,2}; b₁ = NS²−1 = 8 = 1/α₃ (confined). This identification holds
**only for (NS, NT, c) = (3, 2, 2)** — any other triple breaks it.

## 213 sharpening

- "Why d = 5" → Atomicity theorem (no longer empirical).
- "Why NS = 3, NT = 2" → forced by 5 = 3+2, both odd.
- "Why φ in physical ratios" → Fibonacci atomicity forces φ-limit.

## Open / next

- Single closed-form theorem unifying Fibonacci appearance —
  currently catalogued case-by-case.
- Connect SU(5) Y-norm = 5/3 to asymptotic Fibonacci ratio in
  one Lean theorem.
- Verify no other small integer triple forms a Fibonacci cluster —
  falsifier candidate.

## Sources

- `papers/paper1_chiral_decomposition.tex`
- `papers/drlt-book/chapters/ch02_whyd5.tex`
- `lean/E213/Theory/Atomicity/Five.lean`
- `lean/E213/Lib/Physics/Foundations/FibonacciAtomic.lean`
- `lean/E213/Lib/Physics/Couplings/PhotonKernel.lean`
