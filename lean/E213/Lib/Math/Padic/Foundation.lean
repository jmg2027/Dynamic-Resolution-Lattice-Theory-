import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Foundation (G120 Phase 1 starter)

**Status**: STARTER — foundational types and roadmap.  Concrete proofs
to be filled in subsequent sessions per the G120 plan.

See `research-notes/G120_real213_padic_research_direction.md` for the
full campaign structure.

## Goals

Build a 213-native, ∅-axiom construction of the p-adic integers
`ℤ_p` and (later) p-adic numbers `ℚ_p`.  Reuse the G119 Phase 3.3
infrastructure (F_p arithmetic, Bezout, FLT, F_{p²}) without
introducing any new axioms.

## Phase 1 plan (this file)

  · `ZpDigit p` — single p-adic digit (= `Fin p`)
  · `ZpSeq p`   — p-adic integer as infinite digit sequence
  · `ZpSeq.trunc` — truncation to ℤ/p^n
  · `ZpSeq.zero`, `ZpSeq.one`, `ZpSeq.neg_one` — canonical elements
  · `ZpSeq.eq_mod_pn` — equality up to truncation

All declarations must be PURE (#print axioms ... → "does not depend
on any axioms").

## Naming

Module path: `E213.Lib.Math.Padic.Foundation`
Namespace:   `E213.Lib.Math.Padic`

All declarations PURE.
-/

namespace E213.Lib.Math.Padic

/-- A single p-adic digit: an element of {0, 1, ..., p-1}.
    PURE (definitionally `Fin p`). -/
abbrev ZpDigit (p : Nat) : Type := Fin p

/-- A p-adic integer as an infinite digit sequence (least-significant
    digit first).  `digits k : ZpDigit p` is the k-th digit
    in the base-p expansion.

    Conceptually: `x = Σ_{k=0}^{∞} digits k · p^k` in ℤ_p.

    PURE structure (just a function Nat → Fin p). -/
structure ZpSeq (p : Nat) where
  digits : Nat → ZpDigit p

/-- Truncation: read the first `n` digits and assemble as
    `Σ_{k=0}^{n-1} digits k · p^k ∈ ℤ/p^n` (encoded as Nat).

    By induction on `n`:
      · `trunc x 0 = 0`
      · `trunc x (n+1) = trunc x n + digits n · p^n`

    PURE. -/
def ZpSeq.trunc {p : Nat} (x : ZpSeq p) : Nat → Nat
  | 0 => 0
  | n + 1 => x.trunc n + (x.digits n).val * p^n

/-! ## Canonical p-adic integers

`zero`, `one`, `neg_one` (which is `(p-1, p-1, p-1, ...)` in our
encoding, i.e., the "all-digits-(p-1)" sequence corresponding to
the formal sum `Σ (p-1)·p^k = -1` in ℤ_p).
-/

/-- The p-adic zero: all digits zero. -/
def ZpSeq.zero (p : Nat) (hp : 0 < p) : ZpSeq p where
  digits := fun _ => ⟨0, hp⟩

/-- The p-adic one: first digit 1, rest zero.  Requires `1 < p`. -/
def ZpSeq.one (p : Nat) (hp : 1 < p) : ZpSeq p where
  digits := fun k => if k = 0 then ⟨1, hp⟩ else ⟨0, Nat.lt_of_succ_lt hp⟩

/-- The p-adic `-1`: all digits `p-1`.  In ℤ_p, this represents
    `Σ (p-1)·p^k = (p-1)/(1-p) = -1` (formal sum).

    Requires `0 < p` so `p - 1 < p`. -/
def ZpSeq.neg_one (p : Nat) (hp : 0 < p) : ZpSeq p where
  digits := fun _ => ⟨p - 1, Nat.sub_lt hp Nat.one_pos⟩

/-! ## Equality up to truncation -/

/-- Two p-adic integers agree to `n` digits if their first `n`
    digits match.  Equivalent to `x.trunc n = y.trunc n`. -/
def ZpSeq.eq_mod_pn {p : Nat} (x y : ZpSeq p) (n : Nat) : Prop :=
  ∀ k, k < n → x.digits k = y.digits k

/-! ## Sanity / smoke -/

/-- Smoke: `zero 5 (by decide)` truncates to 0 at all levels. -/
theorem ZpSeq.trunc_zero (p : Nat) (hp : 0 < p) :
    ∀ n, (ZpSeq.zero p hp).trunc n = 0
  | 0 => rfl
  | n + 1 => by
    show (ZpSeq.zero p hp).trunc n + ((ZpSeq.zero p hp).digits n).val * p^n = 0
    rw [trunc_zero p hp n]
    show 0 + 0 * p^n = 0
    rw [Nat.zero_mul, Nat.add_zero]

/-- Smoke: `one 5 (by decide)` truncates to 1 at level ≥ 1. -/
theorem ZpSeq.trunc_one_at_one (p : Nat) (hp : 1 < p) :
    (ZpSeq.one p hp).trunc 1 = 1 := by
  show 0 + ((ZpSeq.one p hp).digits 0).val * p^0 = 1
  show 0 + 1 * p^0 = 1
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]

/-! ## Phase 1 TODO list

Next session: implement these helpers and prove they're PURE.

  · `ZpSeq.trunc_lt_p_pow` : `x.trunc n < p^n` (for `0 < p`)
    — Justifies the "ℤ/p^n" interpretation.

  · `ZpSeq.eq_mod_pn_iff_trunc` :
      `eq_mod_pn x y n ↔ x.trunc n = y.trunc n`

  · `ZpSeq.digits_of_nat` : embedding Nat → ZpSeq p
    (via base-p expansion of the Nat).

  · Per-prime smoke tests at p = 2, 3, 5, 7.

## Phase 2 preview (next file: Arith.lean)

  · `Zp.add p x y : ZpSeq p` with carry propagation FSM
  · `Zp.add_trunc` : truncation respects addition mod p^n
  · `Zp.mul p x y : ZpSeq p` with digit-by-digit multiplication
  · `Zp.neg p x : ZpSeq p` (= ZpSeq.neg_one + complement)

## Reuse from G119

Carry propagation will rely on:
  · `E213.Meta.Nat.AddMod213.add_mod_gen` for (a + b) % p
  · Carry FSM structure (similar to existing dyadic FSMs)

Multiplication will leverage:
  · `E213.Meta.Nat.MulMod213.mul_mod_pure` for (a * b) % p
  · Distributive expansion

Inverse (Phase 4, Hensel) will reuse:
  · `E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout`
    (G119 Bezout marathon, Part 30)

These are all ∅-axiom PURE, so the resulting p-adic library is
guaranteed PURE by transitivity.
-/

end E213.Lib.Math.Padic
