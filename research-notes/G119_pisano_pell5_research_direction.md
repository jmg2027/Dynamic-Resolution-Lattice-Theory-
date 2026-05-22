# G119 — Pisano period theorem for Pell-5: research direction

The FSM-1 (2) research goal: prove

```lean
theorem pisano_predict_realises_pell_universal :
    ∀ (p : Nat) (hp : 1 < p),
      ∀ k, (pellFSMmod p hp).bits (k + pisano_predict p hp)
            = (pellFSMmod p hp).bits k
```

where `pisano_predict p hp` is the Legendre-symbol-driven formula:

  · `legendre213 5 p = 0` (ramified)  →  predict = `2p`
  · `legendre213 5 p = 1` (split, QR)  →  predict = `(p-1)/2`
  · `legendre213 5 p = 2` (inert, NQR) →  predict = `p+1`

Currently verified empirically for 17 primes via decide
(`Pisano.Predictor17`).  The Part 5 `pisano_period_lift` template
(commit `fc105cd6`) makes adding new primes 1-line each, but the
universal-over-primes form requires the **Pisano period theorem for
the Pell matrix `M = [[2, 1], [1, 1]]`**.

This is **genuine algebraic number theory**, ~5-10 sessions.

## Phase 1 — Algebraic infrastructure (DONE)

**File**: `lean/E213/Lib/Math/DyadicFSM/PellMatrix.lean`

By Cayley-Hamilton, `M² = 3M - I`.  So every power has the form

  **M^k = a_k · M + b_k · I**

with `(a_0, b_0) = (0, 1)`, `(a_1, b_1) = (1, 0)`, and recurrence

  **(a_{k+1}, b_{k+1}) = (3·a_k + b_k mod p, -a_k mod p)**.

Lean realisation:
  · `pellCoeff p hp k : Fin p × Fin p`
  · `pellCoeffFSM p hp : ArithFSM2 p` (output: `k=0 ∧ b=1` period detector)
  · `pellCoeffFSM_run_eq_pellCoeff` — definitional
  · Smoke tests for p ∈ {3, 5, 11} matching Pisano predictor.

**Status**: PURE, verified.

## Phase 2 — Matrix-order theory (PENDING)

The matrix order of M (smallest N > 0 with `M^N = I`) bounds the
`pellFSMmod p hp` period from above.  The Pisano predictor gives an
upper bound on the matrix order based on the legendre symbol:

  · Ramified (p=5):  M^(2p) = I  (verified: `matrixOrder_5_divides_10`)
  · Split:           M^((p-1)/2) = I
  · Inert:           M^(p+1) = I

### 2.1 — Modular arithmetic prerequisites

  · Fermat's Little Theorem (FLT) for primes:
    `∀ p prime, ∀ a : Fin p, a ≠ 0 → a^(p-1) = 1 in Fin p`.
    Provable from Lean core via a bijection argument (mult by `a` is
    a permutation of `Fin p \ {0}`).  ~2-3 sessions.
  · Modular inverse for primes (corollary of FLT).
  · Order-divides-group-order (Lagrange's theorem on cyclic
    subgroups).  ~1 session given FLT.

### 2.2 — Quadratic residues mod p

  · Decide whether 5 is a QR mod p (= legendre symbol).
  · If QR: construct `sqrt5 : Fin p` such that `sqrt5² = 5 mod p`.
  · `legendre213` already encodes the classification; need the explicit
    sqrt construction (computational; ~0.5 session per prime case).

## Phase 3 — Per-case eigenvalue analysis (PENDING)

### 3.1 — Ramified case (p = 5)

For p = 5, `√5 = 0` in `𝔽_5`, so `φ = (1 + √5)/2 = 1/2`.
The matrix M = `[[2, 1], [1, 1]]` mod 5 has eigenvalues (3 ± 0) / 2 = 3/2.
This is degenerate.  Direct computation: `M^10 = I` mod 5 (decidable).

**Effort**: 0 sessions (done by decide).

### 3.2 — Split case (p ≡ ±1 mod 5, 5 QR)

`√5 ∈ 𝔽_p`, so `φ = (1 + √5)/2 ∈ 𝔽_p`.  M is diagonalizable over
𝔽_p with eigenvalues `φ² = (3 + √5)/2` and `1/φ² = (3 - √5)/2`.

**Key calculation**:

  `(φ²)^((p-1)/2) = φ^(p-1) = 1`  by FLT

Therefore `M^((p-1)/2) = I` in `𝔽_p`.

**Effort**: 1-2 sessions given FLT (Phase 2.1).

### 3.3 — Inert case (p ≡ ±2 mod 5, 5 NQR)

`√5 ∉ 𝔽_p`, but `√5 ∈ 𝔽_{p²} = 𝔽_p[x] / (x² - 5)`.  M acts on
`𝔽_p²` with eigenvalues `φ², 1/φ² ∈ 𝔽_{p²}`.

**Key calculation**:

  Frobenius `σ : x ↦ x^p` sends `√5 ↦ -√5` (since `5^((p-1)/2) = -1`
  when 5 is NQR).  So `σ(φ²) = ((1-√5)/2)² = (3 - √5)/2 = 1/φ²`.

  `(φ²) · σ(φ²) = φ² · (1/φ²) = 1`.

  By FLT in `𝔽_{p²}^*` (which has order `p² - 1`):
  `(φ²)^(p² - 1) = 1`.

  Combined with `(φ²) · σ(φ²) = 1`:  `(φ²)^(p+1) = (φ²) · (φ²)^p = (φ²) · σ(φ²) = 1`.

Therefore `M^(p+1) = I` in `𝔽_p²` (and thus in `𝔽_p²`, since
`M ∈ GL_2(𝔽_p) ⊂ GL_2(𝔽_{p²})`).

**Lean prerequisites**:
  · `𝔽_{p²}` construction: `Fin p × Fin p` with `√5`-multiplication.
  · Frobenius `(a, b) ↦ (a, -b)` on `𝔽_{p²}`.
  · FLT in `𝔽_{p²}^*`.

**Effort**: 3-4 sessions.

## Phase 4 — Universal lift (PENDING)

Combine the three cases via `legendre213` dispatch:

```lean
theorem pellCoeff_pisano_period (p : Nat) (hp : 1 < p) :
    pellCoeff p hp (pisano_predict p hp) = (⟨0, _⟩, ⟨1, _⟩) := by
  rcases hL : (legendre213 5 p (Nat.lt_of_succ_lt hp)).val with
  | 0 => exact ramified_case p hp hL
  | 1 => exact split_case p hp hL
  | _ => exact inert_case p hp hL
```

Lift to `pellFSMmod`:

```lean
theorem pellFSMmod_pisano_period (p : Nat) (hp : 1 < p) :
    ∀ k, (pellFSMmod p hp).bits (k + pisano_predict p hp)
          = (pellFSMmod p hp).bits k := by
  intro k
  -- (1, 1)-orbit ⊂ M-orbit, so period of (1,1) divides matrix order.
  -- pellCoeff_pisano_period gives M^N = I.
  -- Conclude bits(k+N) = bits(k) via run k = pellMat^k · init.
  sorry  -- (final connection, ~0.5 session)
```

**Effort**: 1 session given Phases 2-3.

## Sub-tight cases

For p ∈ {29, 47}, the predictor is non-tight (period = predict / 2
or predict / 3).  These represent sub-orbit structure within the
matrix orbit:

  · p=29 (split): predict = 14, tight = 7.  φ² has order 7 in
    `𝔽_29^*`; the (1, 1) orbit lies in a sub-cyclic subgroup of
    index 2.
  · p=47 (inert): predict = 48, tight = 16.  φ² has order 16 in
    `𝔽_{47²}^*`; sub-orbit of index 3.

The universal theorem **still applies** (predict is an UPPER bound,
not tight).  The sub-orbit refinement (computing the tight period)
is a separate research direction (Galois orbit / cycle structure of
`pellFSMmod`).

## Total effort estimate

  · Phase 1 (infrastructure):  ✓ DONE
  · Phase 2 (FLT + QR):       3-4 sessions
  · Phase 3.1 (ramified):     0 sessions
  · Phase 3.2 (split):        1-2 sessions
  · Phase 3.3 (inert):        3-4 sessions
  · Phase 4 (universal lift): 1 session

**Total**: 8-11 sessions for full theorem.

## Cross-references

  · `lean/E213/Lib/Math/DyadicFSM/PellMatrix.lean` — Phase 1 module.
  · `lean/E213/Lib/Math/DyadicFSM/ArithFSM.lean` — `pellFSMmod` generic def.
  · `lean/E213/Lib/Math/DyadicFSM/Legendre.lean` — `legendre213` decision.
  · `lean/E213/Lib/Math/DyadicFSM/Pisano/Predictor*.lean` — empirical
    verification (17 primes via decide).
  · `research-notes/G118_marathon_deferred_items.md` — overall closure status.

## Progress this session

Phase 1 — algebraic infrastructure (CLOSED):
  · `Lib/Math/DyadicFSM/PellMatrix.lean` — `pellCoeff p hp k` +
    `pellCoeffFSM p hp` + smoke tests at p ∈ {3, 5, 11}.
  · `bridge_smoke_{3, 11}` — verifies pellCoeff/run alignment.

Phase 1 — Cayley-Hamilton infrastructure + bridge (CLOSED):
  · `Lib/Math/DyadicFSM/PellMatrixAction.lean`:
    - `mul_mod_add_mod`, `neg_mod_sub`, `add_zero_mod` (Nat-mod helpers)
    - `nat_arith_{8a_3b, 5a_2b, 9a_decompose, 6a_decompose}` (pure Nat)
    - `action_step_{lhs,rhs}_{1,2}` (component-wise Cayley-Hamilton steps)
    - `action_step_eq` (LHS = RHS at step k+1)
    - **`action_general`** — universal action formula:
      `(pellFSMmod p hp).run k = (3 a_k + b_k mod p, 2 a_k + b_k mod p)`
    - **`pellCoeff_period_implies_pellFSMmod_period`** — BRIDGE THEOREM
    - **`pellCoeff_period_implies_pellFSMmod_bits_period`** (bits version)
  · `Meta/Nat/MulMod213.lean` — PURE mul_mod_*_pure helpers.
  All PURE.

Phase 3.1 — ramified case (CLOSED via bridge):
  · `Lib/Math/DyadicFSM/PellMatrixCases.lean`:
    - **`pell5_ramified_period_via_bridge`** — at p=5, period 10 = 2p
      derived from `pellCoeff 5 _ 10 = (0, 1)` via bridge.

Phase 3.2/3.3 — per-prime smoke tests via bridge (5 primes):
  · `pell{3, 7, 13}_inert_period_via_bridge` — inert case smoke tests
  · `pell{11, 19}_split_period_via_bridge` — split case smoke tests
  All derived from `pellCoeff p hp N = (0, 1)` decides via the bridge.

Empirical chain extension (Predictor20 → Predictor23):
  · 17 → 23 primes covered via `pisano_period_lift` template.
  · Sub-tight pattern (4 of 23): p ∈ {29, 47, 89, 101}.

Sub-tight pattern emerging (4 of 23):
  p=29  (split, ×2)
  p=47  (inert, ×3)
  p=89  (split, ×2)
  p=101 (split, ×2)

All 3 split sub-tight primes are p ≡ 1 (mod 4) AND p ≡ 1 (mod 5).
The (1, 1) initial state lies in an index-2 sub-cyclic subgroup of
the multiplicative group generated by `φ²` in `𝔽_p^*`.

## What the bridge theorem buys

The full Pisano theorem reduces to:

  **Conjecture (FSM-1 ∀p)**:  ∀ p (hp : 1 < p),
    `pellCoeff p hp (pisano_predict p hp) = (0, 1)`.

This is now a CLEAN finite-group-theory statement about the matrix
M = [[2, 1], [1, 1]] in GL_2(𝔽_p), independent of the FSM machinery.

The remaining Phase 2 (FLT + QR) and Phase 3.2/3.3 (legendre dispatch)
proofs target this single conjecture; the bridge theorem then closes
the universal Pisano period theorem for pellFSMmod.

For each specific prime, the bridge already makes the per-prime FSM
period claim derivable via `decide` on pellCoeff, demonstrated by
the 5+ smoke tests in PellMatrixCases.

## Hand-off

This research direction is **open-ended**.  Subsequent sessions can
pick up at any Phase 2-4 sub-goal.  The Phase 1 infrastructure is in
place and ∅-axiom-clean.

## Phase 2 seed (this session)

`E213.Meta.Nat.ModPow213` introduced — 213-native modular
exponentiation toward FLT.  10 PURE declarations:

  · `modPow p a k`        : Nat — `a^k mod p`, recursive on k.
  · `modPow_zero`         — definitional.
  · `modPow_succ`         — definitional.
  · `modPow_one`          : `modPow p a 1 = a % p`.
  · `modPow_lt`           : `0 < p → modPow p a k < p`.
  · `modPow_mod_left`     : `modPow p (a % p) k = modPow p a k`.
  · `modPow_one_base`     : `modPow p 1 k = 1 % p`.
  · `modPow_add`          : `m+n` decomposition.
  · `modPow_mul`          : `m*n` decomposition.
  · `modPow_eq_one_pow`   : witness-propagation —
       `modPow p a m = 1 % p → modPow p a (m*n) = 1 % p`.

The `modPow_eq_one_pow` lemma is the *consumer-side* form: once any
period witness is established for a (whether from FLT proper or from
QR refinement), all multiples of that period inherit `≡ 1 (mod p)`.

What this does NOT yet give:
  · The initial witness `a^m = 1 (mod p)` for some specific m.
  · The Lagrange-style claim that `m | (p-1)` for gcd(a, p) = 1.
  · Quadratic-residue refinement `m | (p-1)/2`.

These remain the substantive Phase 2 work.

Immediate next steps (lowest blocker):
  1. **Lagrange's theorem in `Fin p^*`** for prime p — define
     cyclic subgroup of an element, then count cosets.
  2. **Modular inverse via extended Euclidean** — Lean core has
     `Nat.gcd` but no `Nat.xgcd`; need to add Bezout witnesses.
  3. **FLT primary form** `a^p ≡ a (mod p)` via the
     `(a+1)^p = a^p + ∑_{k=1}^{p-1} C(p,k) a^k + 1` argument
     (uses `p | C(p, k)` for `1 ≤ k ≤ p-1`).
  4. **Pigeonhole existence**: prove that for any a with `gcd(a, p)=1`,
     there exists m > 0 with `modPow p a m = 1 % p`, by tracking
     `modPow p a 0, ..., modPow p a p` and using the recurrence
     bijection.  Weaker than Lagrange but constructively useful.

A `lake build` of `E213.Lib.Math.DyadicFSM.PellMatrix` confirms the
matrix-order detector compiles PURE.  All smoke tests pass via
`decide` or `rfl`.
