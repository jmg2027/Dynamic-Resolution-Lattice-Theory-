import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Foundation (G122 Phase 1 starter)

**Status**: STARTER — foundational types and roadmap.  Concrete proofs
to be filled in subsequent sessions per the G122 plan.

See `research-notes/G122_real213_padic_research_direction.md` for the
full campaign structure.

**Renumbering note**: this campaign was originally labelled G120 on the
incoming branch.  Renumbered to G122 on merge: G120 was already used
for the N_U re-derivation campaign, G121 for geometrization.

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

/-! ## Phase 1 substantive results

Implemented 2026-05-22, building on the smoke tests above.
-/

/-- ★★★★ **Truncation lives in ℤ/p^n**: `x.trunc n < p^n` for all
    `n` and any p-adic sequence `x`.  Justifies the "ℤ/p^n"
    interpretation of truncation.

  Proof by induction on `n`:
    · Base (n = 0): `x.trunc 0 = 0 < 1 = p^0`.
    · Step (n → n+1): use IH + `digits n < p` to bound
      `x.trunc n + (x.digits n).val * p^n < p * p^n = p^(n+1)`. -/
theorem ZpSeq.trunc_lt_p_pow {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ n, x.trunc n < p^n
  | 0 => Nat.one_pos
  | n + 1 => by
    have ih : x.trunc n < p^n := trunc_lt_p_pow hp x n
    have hd : (x.digits n).val < p := (x.digits n).isLt
    have hd_succ : (x.digits n).val + 1 ≤ p := Nat.succ_le_of_lt hd
    show x.trunc n + (x.digits n).val * p^n < p^(n+1)
    have h_pow : p^(n+1) = p * p^n := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [h_pow]
    -- Now goal: x.trunc n + (x.digits n).val * p^n < p * p^n
    have h1 : x.trunc n + (x.digits n).val * p^n
            < p^n + (x.digits n).val * p^n :=
      Nat.add_lt_add_right ih _
    have h2 : p^n + (x.digits n).val * p^n
            = ((x.digits n).val + 1) * p^n := by
      rw [Nat.add_comm, Nat.add_one_mul]
    have h1' : x.trunc n + (x.digits n).val * p^n
             < ((x.digits n).val + 1) * p^n := h2 ▸ h1
    have h3 : ((x.digits n).val + 1) * p^n ≤ p * p^n :=
      Nat.mul_le_mul_right (p^n) hd_succ
    exact Nat.lt_of_lt_of_le h1' h3

/-- ★★★ **Forward direction**: per-digit agreement implies
    truncation agreement.

  `x.eq_mod_pn y n → x.trunc n = y.trunc n`.

  Proof by induction on `n`.  Base: `trunc 0 = 0` for both.
  Step: `trunc (n+1) = trunc n + digits n · p^n`; IH gives
  `trunc n` equality, `eq_mod_pn` provides `digits n` equality. -/
theorem ZpSeq.trunc_eq_of_eq_mod_pn {p : Nat} (x y : ZpSeq p) :
    ∀ n, x.eq_mod_pn y n → x.trunc n = y.trunc n
  | 0, _ => rfl
  | n + 1, h => by
    show x.trunc n + (x.digits n).val * p^n
       = y.trunc n + (y.digits n).val * p^n
    have hn : x.eq_mod_pn y n := fun k hk => h k (Nat.lt_succ_of_lt hk)
    have htn : x.trunc n = y.trunc n :=
      trunc_eq_of_eq_mod_pn x y n hn
    have hdn : x.digits n = y.digits n := h n (Nat.lt_succ_self n)
    rw [htn, hdn]

/-! ## Per-prime smoke tests -/

/-- Smoke: at p = 2, `zero.trunc 5 = 0`. -/
theorem ZpSeq.smoke_zero_p2 : (ZpSeq.zero 2 Nat.zero_lt_two).trunc 5 = 0 :=
  ZpSeq.trunc_zero 2 Nat.zero_lt_two 5

/-- Smoke: at p = 3, `zero.trunc 4 = 0`. -/
theorem ZpSeq.smoke_zero_p3 : (ZpSeq.zero 3 (by decide)).trunc 4 = 0 :=
  ZpSeq.trunc_zero 3 (by decide) 4

/-- Smoke: at p = 5, `one.trunc 1 = 1`. -/
theorem ZpSeq.smoke_one_p5 : (ZpSeq.one 5 (by decide)).trunc 1 = 1 :=
  ZpSeq.trunc_one_at_one 5 (by decide)

/-- Smoke: at p = 7, `one.trunc 1 = 1`. -/
theorem ZpSeq.smoke_one_p7 : (ZpSeq.one 7 (by decide)).trunc 1 = 1 :=
  ZpSeq.trunc_one_at_one 7 (by decide)

/-- Smoke: `trunc_lt_p_pow` at p = 5, n = 3.  For any p-adic
    sequence, `x.trunc 3 < 125`. -/
theorem ZpSeq.smoke_trunc_lt_p3_p5 (x : ZpSeq 5) :
    x.trunc 3 < 125 :=
  ZpSeq.trunc_lt_p_pow (by decide) x 3

/-! ## Phase 2 preview (next file: Arith.lean)

Next-phase content:
  · `Zp.add p x y : ZpSeq p` with carry-propagation FSM
  · `Zp.add_trunc` : truncation respects addition mod p^n
  · `Zp.mul p x y : ZpSeq p` digit-by-digit multiplication
  · `Zp.neg p x : ZpSeq p`

The carry propagation will reuse:
  · `E213.Meta.Nat.AddMod213.add_mod_gen` for `(a + b) % p`

Multiplication will leverage:
  · `E213.Meta.Nat.MulMod213.mul_mod_pure` for `(a * b) % p`

Inverse (Hensel phase) will reuse:
  · `E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout`

All upstream ingredients are ∅-axiom PURE.
-/

end E213.Lib.Math.Padic
