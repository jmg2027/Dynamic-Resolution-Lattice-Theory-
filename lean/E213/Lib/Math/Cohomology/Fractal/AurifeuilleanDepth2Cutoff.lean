import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanLUnbounded

/-!
# Restricted depth-2 cardinality cut-off (Aurifeuillean)

Extends `cutoff_marathon_at_depth_1` from depth 1 to a **restricted**
depth 2: trees of the form `(a op_L b) op_out (c op_R d)` where the
**outer operation `op_out` is `+` or `*` only** (no outer `^`).  Inner
operations `op_L, op_R` can be `+`, `*`, or `^` freely.  Leaves come
from the Hunter generator set `{2, 3, 5}`.

## Why restricted?

Unrestricted depth-2 includes `pow gd (pow gd gd) = 5^3125`
(~2184-digit number) — kernel-intractable.  Strategy 1 of the
cardinality cut-off principle's continuation (Direction A,
`research-notes/G134_cutoff_principle_followups.md` §1) restricts
the outer op to avoid the astronomical case.

## Cardinality bound

Maximum value at restricted depth 2:

  · inner max = `5^5 = 3125` (depth-1 max, `pow gd gd`).
  · outer = `+`: max = `3125 + 3125 = 6250`.
  · outer = `*`: max = `3125 * 3125 = 9_765_625`.

Hence `M_{2,restricted} = 9_765_625` is the uniform upper bound.

## Application

`L_3 = 850_554_441 ≫ 9_765_625`, so `L_3 ∉ HunterValues_{2,restricted}`.
Combined with the depth-1 cut-off (which catches `v > 3125`), this
extends the cut-off from `v > 3125` to `v > 9_765_625` for the
restricted-outer family.

## Honest scope

  · **Proven (PURE)**: depth-2 restricted (outer ∈ {+, ×}) uniform
    bound = 9_765_625; `L_3` is in the asymptotic cut-off.
  · **NOT covered**: outer = `^` (kernel-intractable for exponent
    > 256); structural / Galois-theoretic depth-≥-2 covering of the
    `pow gd (pow gd gd)` family.

## Cross-references

  · `theory/meta/cardinality_cutoff_principle.md` §6 (depth-≥-2
    open frontier).
  · `AurifeuilleanFullCutoff.lean` — depth-1 cut-off capstone.
  · `AurifeuilleanLUnbounded.lean` — L_m chain (m = 1, 3, 7).
-/

set_option maxRecDepth 8192

namespace E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-! ## §1 Encoded value at restricted depth 2 -/

/-- Inner-op selector: `0 ↦ +`, `1 ↦ *`, `2 ↦ ^`. -/
def innerOp (op : Fin 3) (x y : Nat) : Nat :=
  match op.val with
  | 0 => x + y
  | 1 => x * y
  | _ => x ^ y

/-- Outer-op selector (restricted): `0 ↦ +`, `1 ↦ *`.  No `^`. -/
def outerOp (op : Fin 2) (x y : Nat) : Nat :=
  match op.val with
  | 0 => x + y
  | _ => x * y

/-- Restricted depth-2 Hunter value: `(a opL b) opOut (c opR d)`,
    with `opOut ∈ {+, *}` and `opL, opR ∈ {+, *, ^}`.  Leaves
    `a, b, c, d ∈ {2, 3, 5}` (via `Fin 3` index decoder). -/
def depth2Value
    (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2) : Nat :=
  outerOp opOut
    (innerOp opL ([2, 3, 5].get! a.val) ([2, 3, 5].get! b.val))
    (innerOp opR ([2, 3, 5].get! c.val) ([2, 3, 5].get! d.val))

/-! ## §2 Uniform upper bound -/

/-- Restricted-depth-2 uniform upper bound: `M_{2,r} = 3125² = 9_765_625`. -/
def M2r : Nat := 9765625

theorem M2r_value : M2r = 9765625 := rfl

/-- Sanity: `M2r = 5^5 · 5^5 = 3125 · 3125`. -/
theorem M2r_factorisation : M2r = 3125 * 3125 := by decide

/-- ★ **Uniform bound**: every restricted-depth-2 Hunter value is ≤ `M2r`.
    1458 = `3⁴ × 3² × 2` parameter cases enumerated via `decide`. -/
theorem depth2Value_le_M2r :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≤ M2r := by decide

/-! ## §3 Asymptotic cut-off at restricted depth 2 -/

/-- `L_3 = 850_554_441 > M2r = 9_765_625`. -/
theorem L3_exceeds_M2r : M2r < 850554441 := by decide

/-- ★ **Asymptotic restricted-depth-2 cut-off**: any value strictly
    greater than `M2r` is not a restricted-depth-2 Hunter value. -/
theorem asymptotic_cutoff_at_depth_2_restricted :
    ∀ (v : Nat), M2r < v →
      ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
        depth2Value a b c d opL opR opOut ≠ v := by
  intro v hv a b c d opL opR opOut hEq
  have hb := depth2Value_le_M2r a b c d opL opR opOut
  rw [hEq] at hb
  exact absurd hb (Nat.not_le_of_lt hv)

/-- **Specific application**: `L_3 = 850_554_441 ∉ HunterValues_{2,r}`. -/
theorem L3_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ 850554441 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted 850554441 L3_exceeds_M2r
      a b c d opL opR opOut

/-- **Wider application**: `L_7 ≈ 5.27 × 10⁵⁸ ∉ HunterValues_{2,r}`. -/
theorem L7_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut
        ≠ E213.Lib.Math.Cohomology.Fractal.AurifeuilleanLUnbounded.Lval 7 := by
  intro a b c d opL opR opOut
  have hb := depth2Value_le_M2r a b c d opL opR opOut
  intro hEq
  rw [hEq] at hb
  -- M2r = 9765625 ≪ L_7 (59 digits)
  have hL7 : M2r < E213.Lib.Math.Cohomology.Fractal.AurifeuilleanLUnbounded.Lval 7 :=
    by decide
  exact absurd hb (Nat.not_le_of_lt hL7)

/-! ## §4 Capstone -/

/-- ★★★ **Capstone for Direction A** (restricted depth-2 cut-off).

    Bundles:
      (1) the uniform bound `M2r = 9_765_625`,
      (2) the asymptotic cut-off for all `v > M2r`,
      (3) the concrete witness `L_3 ∉ HunterValues_{2,r}`. -/
theorem capstone :
    -- uniform bound on restricted-depth-2 values
    (∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
       depth2Value a b c d opL opR opOut ≤ M2r)
    -- asymptotic cut-off for all v > M2r
    ∧ (∀ (v : Nat), M2r < v →
         ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
           depth2Value a b c d opL opR opOut ≠ v)
    -- L_3 specifically excluded
    ∧ (∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
         depth2Value a b c d opL opR opOut ≠ 850554441) :=
  ⟨depth2Value_le_M2r, asymptotic_cutoff_at_depth_2_restricted,
   L3_not_at_depth_2_restricted⟩

/-! ## §5 Open frontier — unrestricted depth 2

    Removing the outer-op restriction (allowing `opOut = ^`) breaks
    kernel feasibility: `(pow gd gd)^(pow gd gd) = 3125^3125` exceeds
    Lean's exponentiation threshold (256).  Two routes for future
    work:

      1. **Algebraic incompatibility**: prove `L_3 = 850_554_441` has
         a prime factorisation incompatible with `5^k` for any `k`
         (would need `850_554_441` ≠ `5^k` for all `k`).  Combined
         with structural exclusion of mixed-prime depth-2 values,
         this would close the depth-2 unrestricted cut-off without
         enumeration.

      2. **Bounded-exponent variant**: restrict `opOut = ^` to
         specific exponent values (e.g., outer = `^` with exponent
         ≤ 5).  Reduces kernel cost while still capturing some
         outer-pow cases.

    Both are Direction A continuation tasks. -/

end E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff
