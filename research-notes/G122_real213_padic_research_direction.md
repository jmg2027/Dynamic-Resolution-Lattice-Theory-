# G122 — Real213-p-adic: research direction

*(Renumbered on merge: originally proposed as G120 on the
`claude/lean4-ast-patterns-g1gWN` branch.  G120 was already used for the
N_U re-derivation campaign (closed 2026-05-22) and G121 for the
Geometrization closure, so this campaign takes G122.)*

The goal: build **`Real213-p-adic`** — a 213-native, ∅-axiom construction
of the p-adic numbers `ℤ_p` and `ℚ_p`, leveraging the G119 Phase 3.3
infrastructure (F_p arithmetic, Bezout, FLT, F_{p²}, Frobenius).

This is a **5-8 session campaign** building on the modular-arithmetic
library produced during G119 (Parts 28-58).

## Why this matters

DRLT context:
  · Current FSM framework is **2-adic flavored** (dyadic bit-streams).
  · `ResolutionLimit` spec uses `N_U = d^(d²) = 5^25` — base-5
    finite-resolution structure.
  · Real213-p-adic generalizes the resolution lattice from base 2
    to arbitrary prime base p, giving a richer "discrete real"
    structure.

Mathematical context:
  · Mathlib's `Padic` is ~2000 lines on top of `Cauchy` completion
    machinery that requires `Classical.choice` and various other
    axioms.
  · **No known ∅-axiom construction of p-adic numbers exists**
    (Mathlib's brings propext, Quot.sound, Classical).
  · 213-native Real213-p-adic would be the first.

## Reusable infrastructure from G119 (already PURE)

| Component | Location | Use in p-adic |
|-----------|----------|---------------|
| `add_mod_gen` (a+b) % p | AddMod213 | digit-by-digit addition with carry |
| `mul_mod_pure` (a*b) % p | MulMod213 | digit multiplication |
| `mul_p_mod_eq_zero` | ChoosePrime | p-adic zero recognition |
| `modBezout`, `modInverseFromBezout` | ModBezout/Invariant | Hensel inverse |
| `universal_flt_main`: a^(p-1) ≡ 1 | UniversalFLT | Teichmüller / Frobenius |
| `freshman_dream`: (a+1)^p ≡ a^p + 1 | FLT/FreshmanDream | Frobenius automorphism |
| F_{p²} = F_p[x]/(x²-D) full ring | FP2Sqrt5 | Quadratic extensions |
| Frobenius σ: (a, b) ↦ (a, -b) | FP2Sqrt5 | p-adic Frobenius (lifted) |
| `phiFP2_pow_p_eq_frob`: x^p = σ(x) | UniversalPhase33 | Teichmüller lifts |

These give us essentially **all the arithmetic substrate** for p-adic
numbers in ∅-axiom form.

## Phase 1 — ZpDigit + ZpSeq foundation (1-2 sessions)

**File**: `lean/E213/Lib/Math/Padic/Foundation.lean` (new)

```lean
-- A single p-adic digit
abbrev ZpDigit (p : Nat) := Fin p

-- p-adic integer as infinite digit sequence (LSB first)
structure ZpSeq (p : Nat) where
  digits : Nat → ZpDigit p

-- Truncation to ℤ/p^n
def ZpSeq.trunc (p : Nat) (x : ZpSeq p) (n : Nat) : Nat :=
  -- Σ_{i=0}^{n-1} digits(i) * p^i
  ...
```

**Tasks**:
  · ZpDigit type + canonical operations.
  · ZpSeq type + truncation to ℤ/p^n.
  · `Zp.zero`, `Zp.one`, `Zp.neg_one := λ _ => ⟨p-1, _⟩`.
  · Equality up to truncation: `eq_mod_pn : ZpSeq → ZpSeq → Nat → Prop`.

## Phase 2 — Arithmetic operations (1-2 sessions)

**File**: `lean/E213/Lib/Math/Padic/Arith.lean` (new)

```lean
-- p-adic addition with carry propagation
def Zp.add (p : Nat) (x y : ZpSeq p) : ZpSeq p :=
  -- Use mod-p add_mod_gen + carry FSM
  ...

-- p-adic multiplication (FSM-style)
def Zp.mul (p : Nat) (x y : ZpSeq p) : ZpSeq p := ...
```

**Tasks**:
  · `Zp.add` — carry propagation via `add_mod_gen`.
  · `Zp.mul` — distributive accumulation; reuses `mul_mod_pure`.
  · Truncation lemmas: `(x + y).trunc n = (x.trunc n + y.trunc n) % p^n`.
  · `Zp.neg` — via `p^n - x.trunc n` style or all-(p-1)-add-1 trick.

## Phase 3 — p-adic norm + valuation (1 session)

**File**: `lean/E213/Lib/Math/Padic/Norm.lean` (new)

```lean
-- p-adic valuation: index of first nonzero digit (or ∞ if x = 0)
def Zp.val (p : Nat) (x : ZpSeq p) : WithTop Nat :=
  -- Find smallest n with digits(n) ≠ 0
  ...

-- p-adic norm: |x|_p = p^{-val(x)} (or 0)
-- Encoded as a pair (exponent, sign) in ∅-axiom form.
```

**Tasks**:
  · `Zp.val` definition + characterization.
  · `val_add ≥ min` (non-Archimedean property).
  · `val_mul = val + val` (multiplicativity).

## Phase 4 — Hensel's lemma + inverses (2 sessions)

**File**: `lean/E213/Lib/Math/Padic/Hensel.lean` (new)

```lean
-- Hensel's lemma: if f(a₀) ≡ 0 mod p ∧ f'(a₀) ≢ 0 mod p,
-- then there is a unique a ∈ ℤ_p with f(a) = 0 and a ≡ a₀ mod p.
theorem hensel_lift
    (p : Nat) (hp : 1 < p)
    (f f' : ZpSeq p → ZpSeq p)
    (h_deriv : ...)
    (a₀ : Fin p)
    (h_root_mod : (f ⟨..a₀..⟩).trunc 1 = 0)
    (h_deriv_nonzero : (f' ⟨..a₀..⟩).trunc 1 ≠ 0) :
    ∃! a : ZpSeq p, f a = 0 ∧ a.trunc 1 = a₀.val
```

**Tasks**:
  · Multiplicative inverse: `Zp.inv x` for `val(x) = 0`
    (via Hensel applied to `f(y) = xy - 1`).
  · Reuses **G119's `modInverseFromBezout`** for the base step
    (Hensel iterates Bezout lifts).
  · Square root lifting (for `Real213-p-adic` extensions).

## Phase 5 — ℚ_p localization (1 session)

**File**: `lean/E213/Lib/Math/Padic/Field.lean` (new)

```lean
-- ℚ_p as ℤ_p[1/p], encoded as (digits, shift)
structure QpSeq (p : Nat) where
  digits : Nat → ZpDigit p
  shift : Int   -- negative shift = ×p^|shift|
```

**Tasks**:
  · `QpSeq` type.
  · Operations lifted from `ZpSeq`.
  · Field structure (every nonzero has inverse).

## Phase 6 — DRLT integration (1-2 sessions)

**File**: `lean/E213/Lib/Math/Padic/DRLT.lean` (new)

Tie back to DRLT:
  · `ResolutionLimit` lift: how `N_U = 5^25` finite resolution
    fits inside `ZpSeq 5` (5-adic) infinite stream.
  · `pellFSMmod_padic`: p-adic version of pellFSMmod.  Universal
    over arbitrary p (without per-prime decide).
  · Connection to physics: any p-adic observable in DRLT.

## Total effort estimate

  · Phase 1 (foundation):    1-2 sessions
  · Phase 2 (arithmetic):    1-2 sessions
  · Phase 3 (norm/val):      1 session
  · Phase 4 (Hensel):        2 sessions
  · Phase 5 (ℚ_p):           1 session
  · Phase 6 (DRLT integration): 1-2 sessions
  · **Total**: ~6-10 sessions

## ∅-axiom guarantees

Every component must satisfy:
  · `#print axioms ...` → "does not depend on any axioms"
  · No `propext`, `Quot.sound`, `Classical.choice`, `native_decide`
  · No mathlib imports
  · Builds on G119's PURE library (no DIRTY transitively)

## Naming convention

Module hierarchy:
```
lean/E213/Lib/Math/Padic/
  Foundation.lean      -- ZpDigit, ZpSeq, truncation
  Arith.lean           -- Zp.add, Zp.mul, Zp.neg
  Norm.lean            -- Zp.val, |·|_p
  Hensel.lean          -- Hensel lifting, inverses
  Field.lean           -- QpSeq (ℚ_p)
  DRLT.lean            -- DRLT integration
```

Namespace: `E213.Lib.Math.Padic`.

## Cross-references (G119 deps that we'll lean on)

```
E213.Meta.Nat.AddMod213             -- add_mod_gen, mod_mod, zero_mod
E213.Meta.Nat.MulMod213             -- mul_mod_pure, mul_mod_*_pure
E213.Meta.Tactic.NatHelper          -- mul_assoc, add_mul, sub_add_cancel
E213.Lib.Math.ModArith.ModBezout    -- modBezout, xgcd
E213.Lib.Math.ModArith.ModBezoutInvariant -- modInverseFromBezout, mod_cancel_right
E213.Lib.Math.ModArith.UniversalFLT -- universal_flt_main, universal_freshman_dream
E213.Lib.Math.DyadicFSM.FLT.*       -- choose, freshman_dream, flt_main
E213.Lib.Math.ModArith.FP2Sqrt5     -- F_{p²} (for quadratic extensions over ℤ_p)
```

## Anchor result (5-adic specifically)

Since DRLT uses `N_U = 5^25`, the **5-adic Real213** is especially
relevant.  Phase 6 anchor:

```lean
-- 5-adic finite-resolution lift of N_U
theorem nU_lifts_to_Z5_canonically :
    ∀ n ≤ 25, (canonical_5adic_NU).trunc n = ... := ...
```

This gives a concrete bridge from finite-resolution DRLT lattice
to infinite-precision 5-adic continuum.  Whether this "infinite"
is operationally meaningful in DRLT — or just a formal extension
beyond the resolution limit — is itself a research question
(see `RESOLUTION_LIMIT_SPEC.md` §3).

## Open questions

  · **Does Real213-p-adic respect ResolutionLimit?**
    The first 25 digits in 5-adic form are physical; beyond?
    Possibly a residue-Lens choice issue.
  · **p-adic FSM theory**: generalize dyadic FSMs to base-p.
    Pell FSM at base p?
  · **L-functions / zeta**: with p-adic infrastructure, could
    investigate p-adic L-functions in 213-native form.
    Probably another G-campaign.

## Hand-off

Starter file scaffolded at `lean/E213/Lib/Math/Padic/Foundation.lean`
with `ZpDigit` type + `ZpSeq` skeleton + roadmap comments.
Next session: implement Phase 1 (truncation + zero/one/neg_one).

---

## Phase 1 closure log (this session)

**`lean/E213/Lib/Math/Padic/Foundation.lean`** (16 PURE):

  · `ZpDigit`, `ZpSeq` types + `trunc` (LSB-first base-p sum).
  · Canonical: `zero`, `one`, `neg_one` (= all-`(p-1)`).
  · `eq_mod_pn` — digit-by-digit agreement predicate.
  · `trunc_lt_p_pow` — `x.trunc n < p^n` (justifies ℤ/p^n
    interpretation).
  · `trunc_eq_of_eq_mod_pn` / `trunc_succ_inj` /
    `eq_mod_pn_of_trunc_eq` — backward iff via mod-p^n
    cancellation + per-digit `mul_left_cancel_pos`.
  · `eq_mod_pn_iff_trunc` — the full iff.
  · `digits_of_nat` — embedding `ℕ ↪ ZpSeq` (k-th digit
    `(n / p^k) % p`).
  · 16 per-prime smokes at p ∈ {2, 3, 5, 7}.

## Phase 2 partial closure (this session)

**`lean/E213/Lib/Math/Padic/Arith.lean`** (15 PURE):

  · `Zp.carry` — recursive carry FSM (initial 0, step
    `(d_x + d_y + carry) / p`).
  · `Zp.add` — digit-by-digit + carry; total function.
  · `Zp.add_trunc_eq` — structural identity
        `x.trunc n + y.trunc n
          = (Zp.add x y).trunc n + carry n · p^n`
    proved by induction with calc + a `split_mul_pow` helper
    routed through PURE `div_add_mod`.
  · `Zp.add_trunc` — the ring-quotient theorem
        `(Zp.add x y).trunc n = (x.trunc n + y.trunc n) % p^n`.
    Truncation `ZpSeq p → ℤ/p^n` is an additive homomorphism.
  · `Zp.complement` — digit-wise `p - 1 - d`.
  · `Zp.neg` — `complement x + one`.
  · `Zp.carry_x_complement` — when summing `x + complement x`,
    every digit-pair sums to `p - 1 < p`, so carry stays at 0
    for all positions.
  · `Zp.add_complement_digit` — every digit of `x + complement x`
    equals `p - 1`, i.e., the sum is the all-`(p-1)` sequence
    (= `-1` in ℤ_p).  Structural reason `-x := complement x + 1`
    works: `x + (-x) = neg_one + one = 0` in ℤ_p (carry cascades).
  · Smokes for `add` / `neg`.

**Padic total**: 47 PURE / 0 DIRTY.

## Phase 2 remaining work

  · `Zp.mul` — DEFINITIONS COMPLETE, identity laws proven, n = 1
    truncation case proven.  Multiplicative identity established
    both sides: `mul_one_{left,right}_digit`.  Absorbing zero
    established both sides: `mul_zero_{left,right}_digit`.
    Base case for truncation correctness: `Zp.mul_trunc_one`.

  · `mul_trunc` decomposition status (this session):

    - Step 1 (structural identity): DONE.
        `Zp.mulSumRaw_eq_trunc`:
            mulSumRaw x y n = (Zp.mul x y).trunc n + mulCarry n · p^n
        `Zp.mulSumRaw_mod_eq_trunc`:
            mulSumRaw x y n % p^n = (Zp.mul x y).trunc n

    - Step 2 (bilinear decomposition): PARTIAL.
        `Zp.colSum / bilinSum` + closed forms
        `colSum i b = (x.digits i).val · p^i · y.trunc b`
        `bilinSum b a = x.trunc a · y.trunc b`
        give us `x.trunc n · y.trunc n` expressed as the 2D sum
        Σ_{i<n, j<n} x_i · y_j · p^(i+j).

    - Step 3 (bridge): PENDING.
        Need `bilinSum n n % p^n = mulSumRaw n % p^n`.

  · The bridge.  Conceptually `bilinSum n n` sums over the full
    n × n square in (i, j) space, while `mulSumRaw n` sums over
    the diagonal region `i + j < n`.  The difference (the
    "off-diagonal" pairs with `i + j ≥ n`) contributes only terms
    divisible by `p^n`, so they vanish mod `p^n`.

  · The recurrence governing this bridge (computed analytically;
    proof-in-Lean pending):
        bilinDiff 0 = 0
        bilinDiff (n+1) = (bilinDiff n
                            + x.trunc n · y_n + y.trunc n · x_n
                            + x_n · y_n · p^n
                            - mulRaw n) / p
    where `bilinDiff n := (bilinSum n n − mulSumRaw n) / p^n`.
    The recurrence's divisibility by `p` relies on a non-trivial
    congruence:
        bilinDiff n ≡ Σ_{1 ≤ i ≤ n-1} x_i · y_{n-i}  (mod p)
    — the "middle" of `mulRaw n` matches `bilinDiff n mod p`.
    Verified for `n ∈ {0, 1, 2, 3}`; general proof in Lean
    requires either a strong invariant on `bilinDiff` (mod-p
    structural condition) or an alternate definition of
    `bilinDiff` as an explicit sum over off-diagonal pairs.
  · `Zp.neg_add_self` — full algebraic statement
    `Zp.add x (Zp.neg x) = Zp.zero` (sequence equality, requires
    funext-by-design pattern OR per-truncation rephrasing).
    Cleanest version: `(Zp.add x (Zp.neg x)).trunc n = 0`.

## Phase 3 starter (this session)

**`lean/E213/Lib/Math/Padic/Norm.lean`** (9 PURE):

  · `Zp.valAtLeast x n` — predicate "every digit < n is zero".
    PURE alternative to `v_p(x) ≥ n` (avoiding `WithTop`).
  · `Zp.valAtLeast_zero`, `valAtLeast_mono` (downward closed).
  · `Zp.valAtLeast_iff_trunc` — `valAtLeast x n ↔ x.trunc n = 0`
    (via Foundation `eq_mod_pn` ↔ `trunc` bridge).
  · `Zp.valEq x n` — exact valuation: `valAtLeast x n ∧ x.digits n ≠ 0`.
  · `Zp.valEq_unique` — uniqueness (Nat trichotomy + contradiction).

This gives a propositional handle on the p-adic valuation suitable
for Hensel-style induction without committing to an extended
numeric type.

## Updated phase outline (post-session)

| Phase | Status |
|---|---|
| 1. Foundation | DONE (16 PURE) |
| 2. Arith — add + neg | DONE (15 PURE with full truncation correctness; comm + identity at digit level) |
| 2'. Arith — mul | LARGE PROGRESS (37 PURE: defs + identity-laws both sides + absorbing-zero both sides + `mul_trunc_one` foothold + `mul_trunc` step 1 (structural identity) + step 2 partial (bilinear sum machinery); bridge step 3 pending) |
| 3. Norm + valuation | STARTER (9 PURE; `valAtLeast` + `valEq` + uniqueness) |
| 4. Hensel lifting | PENDING |
| 5. ℚ_p localization | PENDING |
| 6. DRLT integration (5-adic N_U lift) | PENDING |

**This session's deliverables**: 93 PURE declarations across 3
Padic modules (Foundation + Arith + Norm).  Branch
`claude/g122-real213-p-adic-LwxL9` pushed across multiple commits.

## Bridge analysis (recorded for next session)

For the `mul_trunc` theorem, we have steps 1 and 2-partial; the
remaining piece is the **diagonal-vs-square bridge**:

  `bilinSum p x y n n % p^n = mulSumRaw p x y n % p^n`

Equivalent existence form:
  `∃ q, bilinSum p x y n n = mulSumRaw p x y n + q · p^n`.

The "right" q at level n is the **off-diagonal sum**:
  `q_n = Σ over (i, j) with i < n, j < n, i+j ≥ n of x_i · y_j · p^{i+j-n}`.

Reparametrize by `i` (rows) and `m = j - (n - i)`, so j = n-i+m and
m ranges from 0 to i-1.  Then q_n = `Σ_{i<n} x_i · Σ_{m<i} y_{n-i+m} · p^m`.

Verified by hand for n ∈ {0, 1, 2, 3}: matches q_0 = 0, q_1 = 0,
q_2 = x_1·y_1, q_3 = x_1·y_2 + x_2·y_1 + x_2·y_2·p.

**Induction complication**: q_{n+1} doesn't relate to q_n via a
simple recurrence because the `n` index appears inside `y.digits`
in q's formula.  Specifically, q_n references `y.digits (n - i + m)`,
which shifts when `n → n+1`.

**Strategy for next session**: prove the bridge identity by
**partition-of-the-square** rather than by induction on n.
Define a 2D recursive `offDiagSum p x y n (a, b)` parameterized by
the row/col bounds, and decompose `bilinSum n n` directly as
`mulSumRaw n + offDiagSum n (n, n) · p^n` via a sub-induction that
moves the (a, b) bounds one step at a time within a fixed `n`.

Alternatively, work via `Nat.ModEq` machinery if a PURE version
exists (or build one from `add_mul_mod_self_pure`).

---

**Status**: Phase 1 complete + Phase 2 add/neg with full truncation
correctness + digit-level commutativity + Phase 2' multiplication
substantially developed (defs PURE, identity / absorbing-zero
laws both sides, n = 1 truncation foothold) + Phase 3 starter
with valuation predicates.  Next session: prove the general
`Zp.mul_trunc` ring-quotient theorem (analog of `add_trunc`),
then extend toward Hensel lifting + ℚ_p localization.
