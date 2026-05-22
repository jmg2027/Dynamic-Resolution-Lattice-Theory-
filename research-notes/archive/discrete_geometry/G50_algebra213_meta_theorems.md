# G50 — Algebra213 Meta-Theorems

The hierarchical-modular Algebra213 work yields several meta-theorems
about polynomial-identity proofs in Cayley–Dickson (CD) rings.  Here
we articulate them and trace their formalization status.

---

## Context

Cayley–Dickson construction iterates: ℝ → ℂ → ℍ → 𝕆 → 𝕊 → ⋯ each
doubling dim by 2.  At every layer, relevant identities are
polynomial in 2^N Int variables, e.g.,

  * Hurwitz norm-multiplicativity `|uv|² = |u|² · |v|²` at layer 3 (𝕆) =
    8-variable identity with ~100 monomials per side.
  * Associativity `(uv)w = u(vw)` at layer 2 (ℍ) = 12-variable, ~64 terms.

The classical proof methodology — `quad_norm` / `hurwitz_ring` tactics
— flatten each identity to Int polynomial then close via `simp + omega`.
Cost: exponential in CD layer index.  Times out at level 3+.

---

## M1 — Layer Separation Principle (formalization complete)

**Statement.**  Polynomial identities of shape `f(uv) = g(u, v)` in
CD-derived rings can be proved in 3 stages:

  1. **Typeclass abstraction.**  Define `Ring213`/`StarRing213`/
     `IntegerNormed213` over base operations, with the desired
     identities (e.g., `self_mul_conj`) as instance fields.
  2. **Generic theorem.**  Prove `normSq_mul` once, using only
     typeclass axioms (no concrete polynomial expansion).
  3. **Per-instance verification.**  Each concrete ring (ZI, Lipschitz,
     ...) only needs to verify its specific operations satisfy the
     axioms.

Formalization: `lean/E213/Theory/Internal/Algebra213.lean` — typeclass
hierarchy + generic `IntegerNormed213.normSq_mul` PURE.

---

## M2 — Polynomial Avoidance Theorem

**Statement.**  At CD layer N, the polynomial expansion has Θ(2^N)
variables and Θ(4^N) monomials.  The abstract algebra chain via
typeclass projections has length **independent of N**.

**Concrete witness.**  Lipschitz `normSq_mul` (8 Int vars, ~100
monomials per side) is auto-derived from `IntegerNormed213.normSq_mul`
in 9 calc steps, vs. `hurwitz_ring`'s direct polynomial expansion that
times out at the practical heartbeat ceiling.

Formalization: `lean/E213/Lib/Math/CayleyDickson/LipschitzAlgebra213.lean`
+ `LipschitzHeavy.lean` migrations (4 hurwitz_ring DIRTY → 0).

---

## M3 — CD Doubling Functor (formalization in progress)

**Statement.**  Cayley–Dickson doubling

  CDDouble : Type → Type,  CDDouble α := α × α
  
with multiplication `(a, b)·(c, d) := (a·c - d̄·b, d·a + b·c̄)` and
conjugation `(a, b) ↦ (ā, -b)` is a *functor* on commutative *-rings:

  CDDouble : `CommStarRing213` ↦ `StarRing213` (commutativity NOT
                                                  preserved at codomain)
  CDDouble : `CommIntegerNormed213` ↦ `IntegerNormed213`

**Specializations (intended).**
  CDDouble Int = ZI  (with trivial Int conj)
  CDDouble ZI  = Lipschitz
  CDDouble Lipschitz = Cayley   (associativity LOST — see M4)

**Status.**  Skeleton in `lean/E213/Theory/Internal/Algebra213CDDouble.lean`:
  * Structure `CDDouble α` ✓
  * Componentwise `add_assoc'`, `add_comm'`, `add_zero'`, `add_left_neg'` ✓
    (each one-line via `Ring213.X u.re + Ring213.X u.im`)
  * `add_mul'` ✓ (Ring213.add_4_swap_mid)
  * Remaining: `mul_assoc`, `mul_add`, `conj_conj`, `conj_add`,
    `conj_mul` anti, `self_mul_conj`, `ofInt_*` — all derivable from
    base CommStarRing213 algebra; pattern matches Lipschitz instance.

If completed, ZI's instance reduces from ~135 lines to ~10 (just provide
Int's CommStarRing213 instance + invoke functor).

---

## M4 — CD Threshold Theorem (informal)

**Statement.**  CD functor preserves these properties up to specific
thresholds:

| Property | Preserved up to | Breaks at |
|---|---|---|
| Commutativity | ℂ (level 1) | ℍ |
| Associativity | ℍ (level 2) | 𝕆 |
| Alternativity | 𝕆 (level 3) | 𝕊 |
| Norm multiplicativity | 𝕆 (level 3) | 𝕊 (witness: zd_left·zd_right=0) |
| Zero-divisor-freeness | 𝕆 (level 3) | 𝕊 |

**Implication.**  M3's `CDDouble : CommStarRing213 → StarRing213` is the
strongest meta-instance.  For the next layer (𝕆), associativity breaks;
need weaker `AlternativeRing213` typeclass with Moufang-style axioms.
At 𝕊, even alternativity fails — no algebraic structure preserves
norm-multiplicativity.

Formalization: existing `SedenionHeavy.normSq_mul_fails` constitutes
the concrete witness.

---

## M5 — `simp` + `rw` Decomposition for ∅-axiom

**Statement.**  `simp only [PURE_lemmas]` leaks `propext` when **closing**
a goal via internal AC normalization.  But `simp only` used as a
**normalization** step (leaving a residue that `rw` finishes) stays PURE.

**Pattern.**  For polynomial identity `LHS = RHS`:

  1. `simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
                 neg_add, add_mul, mul_add, mul_assoc]` — distribute
     fully, no AC.  This is structural normalization, not closure.
  2. The residue is a sum-permutation difference; closing helper
     selected by structure:
     * `add_4_swap_mid`: 4-term swap (e.g., (A+B) + (Y+Z) =
                                          (A+Y) + (B+Z))
     * `add_4_cycle`: 4-term cyclic permutation
     * `add_5_perm`: 5-term permutation (Eisenstein .re component)
     * Cancellation pair + permutation: 8-term (Eisenstein .im, deferred)

**Implication.**  ∅-axiom proofs of polynomial identities reduce to:
choosing the right reorder helper per residue shape.  The helpers
themselves are short (3–6 line `rw` chains using `add_assoc`,
`add_left_comm`, `add_comm`).

Formalization status: `Algebra213.Ring213.{add_4_swap_mid, add_5_perm}`
PURE; `add_4_cycle` private to LipschitzAlgebra213.

---

## Combined picture

The 5 meta-theorems combined explain *why* the hierarchical typeclass
approach works at all layers ≤ 3:

  1. **M1** says: typeclass abstraction is the right framing.
  2. **M2** says: it's exponentially cheaper than polynomial expansion.
  3. **M3** says: CD doubling is itself a functor — so proofs lift
     automatically.
  4. **M4** delimits applicability: associative threshold = level 3.
  5. **M5** explains the ∅-axiom proof pattern at each level.

For levels ≥ 4 (𝕊, 𝕋, ...), M4 says norm-multiplicativity fails as
a *theorem* (zero divisors witness it).  So the "infinite ladder" of
generic Hurwitz preservation is sharply terminated at 𝕆.  This is
itself a structural insight 213 captures via the meta-theorems: the
CD-derived rings do not extend beyond 𝕆 in a way that preserves
classical algebraic properties.
