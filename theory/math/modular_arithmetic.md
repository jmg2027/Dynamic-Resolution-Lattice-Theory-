# Modular Arithmetic 213

**Status**: Closed (13 files.

## Overview

213-native modular arithmetic: Bézout's identity, GCD via Euclidean
algorithm, modular inverse, Chinese Remainder Theorem.  All
**explicit-witness** (no existential) — Bézout coefficients are
computed, GCD has explicit step bound.

Universal-Pisano marathon (Phase 3.2/3.3 marathon) extends the chapter with:
- An explicit-Nat Bezout via xgcd that universalises modular inverse
- Fermat's Little Theorem (FLT) universal in the prime p, derived
  from a 213-native binomial theorem
- The quadratic field extension `F_{p²} = F_p[√5]` with Frobenius

These three are the algebraic substrate for the Pell-Fibonacci
universal-prime closures in `theory/math/dyadic_fsm.md` (universal-Pisano marathon
Phase 3.2/3.3/4).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/ModArith/` (13 files)
- **Umbrella**: `ModArith.lean`
- **∅-axiom status**: PURE (all 13)

| Group | Files | Topic |
|---|---:|---|
| Bezout / GCD / Euclidean | 6 | `JoinGCD`, `JoinBezout`, `JoinEuclidean`, `JoinCoprime`, `JoinEquivGCD`, `JoinExample` |
| CRT (Lens) | 1 | `LensCRT` |
| Per-modulus PureNat | 2 | `PureNatMod3`, `PureNatMod5` |
| universal-Pisano marathon Bezout / FLT / F_{p²} | 4 | `ModBezout`, `ModBezoutInvariant`, `UniversalFLT`, `FP2Sqrt5` |

## Narrative

### Core (pre-universal-Pisano marathon)

Standard `Nat.gcd` uses Lean's well-founded recursion.  213's
`GCD` is dyadic-FSM-style: explicit step-count bound (≤ log_2 of
smaller input).  Bézout coefficients are returned as part of
the GCD output (not Skolemized).

CRT is used in the universe chain (Step 12: lcm(5, 2) = 30).

### universal-Pisano marathon — Bezout, FLT, F_{p²}

**Explicit-Nat Bezout (`ModBezout`, `ModBezoutInvariant`).** The
extended Euclidean algorithm is reformulated as a `Nat`-valued
xgcd: rather than `(s, t) ∈ ℤ × ℤ`, the algorithm produces
`(u, v) ∈ ℕ × ℕ` together with a sign-bit, satisfying
`u · a = v · b + gcd a b`  or  `v · b = u · a + gcd a b`.
This makes Bezout decidable without any signed-integer machinery
and gives a `modInverseFromBezout : (a p : ℕ) → coprime a p → ℕ`
that the rest of universal-Pisano marathon builds on.

**Universal FLT (`UniversalFLT`).** The chain:

1. **Freshman's dream**: `(a + b)^p ≡ a^p + b^p (mod p)` for any
   prime `p`.  Proved via the binomial theorem combined with a
   key divisibility fact: for `0 < k < p`, the prime `p` divides
   `C(p, k)`.
2. **Binomial theorem** (213-native, `BinomialTheorem`):
   `(a + b)^n = Σ_{k=0}^{n} C(n, k) · a^k · b^{n-k}` using a
   `Sigma`-fold infrastructure.
3. **FLT primary** (`FLTPrimary`): for `a < p`, `a^p ≡ a (mod p)`.
   Proved by induction on `a` using freshman's dream as the step.
4. **FLT main** (`FLTMain`): for `a` coprime to `p`,
   `a^(p-1) ≡ 1 (mod p)`.  Follows from primary + modular inverse.

The chain is fully universal in `p` (any `p` with `1 < p`, with a
primality hypothesis where needed).  Concrete instances verified
at `p ∈ {2, 3, 5, 7, 11}`.

**F_{p²} = F_p[√5] (`FP2Sqrt5`).** Elements `x ∈ F_{p²}` are pairs
`(a, b) : Fin p × Fin p` representing `a + b·√5`.  Multiplication
uses `(a + b√5)(c + d√5) = (ac + 5bd) + (ad + bc)√5` interpreted
mod `p`.  Key results:

- **Ring structure**: additive group + commutative multiplication
  + distributivity (`fp2_ring_axioms`)
- **Frobenius** `φ : F_{p²} → F_{p²}`, `x ↦ x^p`:
  - additive: `(x + y)^p = x^p + y^p`  (`frob_add`, follows from
    freshman's dream in `F_{p²}`)
  - multiplicative: `(x · y)^p = x^p · y^p`  (`frob_mul`)
  - thus a ring homomorphism (`frob_ring_hom`)
- **`√5 ↦ ±√5` under Frobenius**: by FLT in `F_p`,
  `√5^p = √5 · 5^((p-1)/2) = ± √5`, sign = Legendre symbol
  `(5/p)`.  Drives the **split vs inert** dichotomy that the Pell
  closures need.
- **Norm**: `N(a + b√5) = a² − 5b²`.  `N(x · σx) = N(x)` where
  `σ` is the Galois automorphism = Frobenius.
- **Frobenius FLT** (in `F_{p²}`): for `x ∈ F_{p²}` invertible,
  `x^(p²−1) = 1`.  Specialises to FLT in `F_p` and to the
  Pisano-period-prime closures.

The 5 in `F_p[√5]` is forced by `φ = (1 + √5)/2` (golden ratio,
the Pell-matrix eigenvalue from `theory/math/dyadic_fsm.md`'s
Pell story).  Phase 3.3 in DyadicFSM lifts this into the
universal-prime closure of the Pisano-period theorem for Pell.

## F_p[√D] universal in D — closed (FP2SqrtD)

`Lib/Math/ModArith/FP2SqrtD.lean` lifts the Phase 3.3 D=5 algebra
to **arbitrary** `D : Nat`.  32 PURE theorems:

  · Operations parametric in `(D, p)`: `fp2dAdd, fp2dSub, fp2dMul,
    fp2dFrob, fp2dNorm, fp2dPow` and the generator `fp2dSqrtD`.
  · `(√D)² = (D mod p, 0)` (`fp2dSqrtD_sq`).
  · Ring axioms (`fp2dAdd_comm`, `fp2dMul_comm`, zero / one laws).
  · Frobenius `σ(a + b√D) := (a, -b)`:
      - involution (`fp2dFrob_involution`)
      - preserves zero / one (`fp2dFrob_zero`, `fp2dFrob_one`)
      - additive (`fp2dFrob_add`, D-independent)
      - multiplicative (`fp2dFrob_mul`, D-aware — the cross term
        `D · b · d` is preserved by the double sign flip)
  · Norm identity `x · σ(x) = (Norm_D(x), 0)`
    (`fp2dMul_self_frob`) — parametric in D.
  · Specialisation: at `D = 5`, every `fp2d*` matches the
    corresponding `fp2*` in `FP2Sqrt5` on test vectors
    (`fp2dMul_sqrt5_specializes_p7`).
  · Smoke at varied `(D, p)`: `D ∈ {2, 3, 7}`, `p ∈ {7, 11, 13}`.

The Frobenius FLT chain `x^(p² − 1) = 1` in `F_{p²}` and the
Legendre dispatch `√D ↦ (D/p) · √D` are now uniform in D; the
Pell-Fibonacci split / inert structure (Phase 3.3) reads as the
D=5 specialisation of one general theorem.

## Hensel bridge — closed (HenselBridge.lean, 8 PURE)

`Lib/Math/Padic/HenselBridge.lean` makes the `F_p ↪ ℤ_p`
embedding explicit:

  · `fromFp p hp x` lifts a Nat element to a `ZpSeq p` with
    digit-0 = `x mod p`, rest zero.
  · `fromFp_digit_zero`, `fromFp_digit_above` — digit accessors.
  · `invDigit0_of_fromFp` — bridge: the Hensel-lifted inverse's
    digit-0 equals the Bezout modular inverse.
  · `fromFp_inverse_mod` — modular identity `(x mod p) · inv ≡
    1 (mod p)`.
  · ★★★★★ `hensel_bridge_capstone` packages lift + Bezout-match
    + inverse identity.

Reading: the chain `F_p ↪ ℤ_p` is explicit at the Lean level;
every modular structure (FLT, Bezout, F_p[√D]) composes with
`fromFp` + the existing `Zp.invSeq` scaffold to lift into ℤ_p via
Hensel.

## Full F_p[√D] → ℤ_p[√D] lift — closed (ZpSqrtD.lean, 12 PURE)

`Lib/Math/Padic/ZpSqrtD.lean` realises `ℤ_p[√D]` parametric in D:

  `ZpSqrtD p := ZpSeq p × ZpSeq p` represents `a + b·√D`.

  · `zpsd_add p hp x y` — componentwise `Zp.add` (D-independent).
  · `zpsd_mul p hp D x y` — `(ac + D·bd) + (ad + bc)√D` with D
    lifted via `fromFp p hp D`.
  · `zpsd_zero / zpsd_one / zpsd_sqrtD` — canonical constants.
  · `fp2d_to_zpsd p hp x` — embedding `FP2 ↪ ZpSqrtD p` lifting
    each component via `fromFp`.
  · `fp2d_to_zpsd_digit_0_first/second` — digit-0 bridge:
    embedding's digit-0 equals the F_p value mod p.
  · ★★★★★ `zpsd_capstone` packages constants, embedding digit-0,
    and `√D` generator's digit signature.

Reading: the F_p[√D] machinery lifts componentwise to ℤ_p[√D] via
`fromFp`; every F_p[√D] identity has a ℤ_p[√D] analog whose
digit-0 matches.

`Lib/Math/Padic/ZpSqrtDFrob.lean` (8 PURE) adds Frobenius + Norm:

  · `zpsd_frob p hp x := (x.1, Zp.neg p hp x.2)` — Frobenius
    `σ(a + b√D) = a − b√D`.
  · `zpsd_norm p hp D x` — Galois norm `a² − D·b²` via
    `Zp.mul` + `Zp.add` + `Zp.neg`.
  · `zpsd_frob_first` / `zpsd_frob_second` — component identities
    (rfl).
  · ★★★★★ `zpsd_frob_norm_capstone` packages the Frobenius
    component identities + Frobenius-of-zero.

The FP2SqrtD algebraic identities (Frobenius involution,
additivity, multiplicativity, norm = self·conjugate) all have
ℤ_p[√D] analogs via the same `fromFp`-based lift.

## Rigor — ZpSqrtD ring + embedding (16 PURE)

`Lib/Math/Padic/ZpSqrtDRigor.lean` (8 PURE) establishes the
**embedding is a ring homomorphism at digit-0, modulo p**:

  · `zpsd_add_digit_zero_first/second` — digit-0 of zpsd_add =
    `(x.i.digit_0 + y.i.digit_0) mod p`.
  · `zpmul_digit_zero` — digit-0 of `Zp.mul a b` =
    `(a.digit_0 * b.digit_0) mod p`.
  · `zpsd_mul_digit_zero_second` — second-component formula
    `((x.1 · y.2) % p + (x.2 · y.1) % p) % p`.
  · `fp2d_to_zpsd_preserves_add_first/second_mod` — ring-hom
    preservation: `(fp2d_to_zpsd (fp2dAdd x y)).digit_0 % p`
    matches the ℤ_p computation.
  · ★★★★★ `zpsd_rigor_capstone` packages all four.

`Lib/Math/Padic/ZpSqrtDRing.lean` (8 PURE) adds ring axioms:

  · `zpsd_add_comm_digit_zero_first/second` — commutativity of
    zpsd_add at digit-0 (both components).
  · `zpmul_comm_digit_zero` — `Zp.mul` commutativity at digit-0.
  · `zpsd_mul_comm_digit_zero_second` — `zpsd_mul` second-
    component commutativity.
  · `zpsd_zero_components_zero` / `zpsd_one_components_one_zero`
    — zero / one digit-0 values.
  · `zpsd_add_zero_left_first_mod` — zero left-identity (when
    digit-0 < p).
  · ★★★★★ `zpsd_ring_capstone` packages add comm + mul comm +
    zero / one identities.

Reading: ZpSqrtD inherits the FP2SqrtD ring structure at digit-0
rigorously; commutativity / zero / one axioms are Nat-decidable
facts following from the digit-formula machinery + `Nat.add_comm`
/ `Nat.mul_comm`.

## Zp.neg involution — trajectory-pw realisation (16 PURE)

`Lib/Math/Padic/NegInvolution.lean` (6 PURE) closes
`Zp.neg ∘ Zp.neg = id` **at digit-0**:

  · `double_neg_mod_at` — `(p - (p - r) % p) % p = r` for `r < p`.
  · `zp_neg_digit_zero` — `((Zp.neg x).digits 0).val =
    (p - x.digit_0) % p`.
  · `zp_neg_neg_digit_zero` — involution at digit-0.
  · `add_right_cancel_pure` — PURE local re-proof of Lean-core's
    propext-leaking `Nat.add_right_cancel`.

`Lib/Math/Padic/NegInvolutionDigit1.lean` (10 PURE) extends to
digit-1, tracking the **one-step carry chain**:

  · `neg_carry_at_1` — general carry formula `(p - x.digit_0) / p`.
  · `neg_carry_at_1_when_zero / nonzero` — case-split:
    carry = 1 iff x.digit_0 = 0.
  · `div_self_pure` — PURE local `p / p = 1`.
  · `zp_neg_digit_one_when_zero / nonzero` — digit-1 formula by case.
  · ★★★ `zp_neg_neg_digit_one_when_zero / nonzero` — involution at
    digit-1 in both cases.

The trajectory-pw pattern at digit-1 ties the inner carry
(`x.digit_0 = 0`?) to the outer carry
(`(Zp.neg x).digit_0 = 0`?); both flip together, cancelling.

## Full Zp.neg involution via State Accumulator Pattern (9 PURE)

`Lib/Math/Padic/NegInvolutionFull.lean` (5 PURE) + `NegInvolutionPreserve.lean`
(4 PURE) close the **full sequence-level involution** `Zp.neg ∘ Zp.neg = id`
as a pointwise (∀ k) PURE theorem.  The polynomial carry-chain
blow-up that blocked higher-digit involution collapses to
**constant-branching** when carry state is compressed to a single
Bool:

  `all_zero_below x k : Bool := (x.digits 0..k-1 all zero)`

  · `neg_carry_eq_state` — `Zp.carry (complement x) one (k+1) =
    (if all_zero_below x (k+1) then 1 else 0)`.
  · `zp_neg_digit_succ_with_state` — `Zp.neg` digit-k formula
    parametric in the state.
  · ★★★★ `neg_preserves_state` — **preservation invariant**:
    `all_zero_below (Zp.neg x) k = all_zero_below x k` (constant-
    branching induction on k).
  · ★★★★★ `zp_neg_neg_digit_at` — full involution at every
    digit-k.  Case-splits on `all_zero_below x k`; both cases
    collapse to `x.digit_k` via `double_neg_mod_at` (state=true)
    or `sub_sub_cancel` (state=false).
  · `state_accumulator_carry_capstone` + `zp_neg_full_involution_capstone`
    package the framework.

This realises the **funext-blocked sequence-level identity** as
PURE pointwise theorem.  All Lean-core helpers that leak propext
(`Nat.add_right_cancel`, `Nat.div_self`, `Nat.sub_pos_of_lt`) are
re-proved locally via direct induction.

## Open frontier

- ~~**Real213-p-adic**~~ — CLOSED via `HenselBridge.lean`
  (8 PURE) above (skeleton; full F_{p²}-to-ℤ_p[√D] lift is open
  follow-up).
- ~~**Higher quadratic extensions** `F_p[√D]` for general `D`~~ —
  CLOSED via `FP2SqrtD.lean` (32 PURE) above.  Ring + Frobenius
  + Norm parametric in `D`.

## Connection

- `theory/math/universe_chain.md` — CRT decomposition (mod 5, mod 2)
- `theory/math/dyadic_fsm.md` — Pell-Fibonacci universal closures
  (Phase 3.2/3.3/4) consume `UniversalFLT` and `FP2Sqrt5`
- `theory/physics/foundations/atomic_constants.md` — C2 uses
  `Nat.lt` + `Nat.sub` bridges similar to ModArith
