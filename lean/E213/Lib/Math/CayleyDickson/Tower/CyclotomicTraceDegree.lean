import E213.Lib.Math.CayleyDickson.Tower.ExceptionalTraceSeed

/-!
# Why `√2` and `√5`?  The cyclotomic-degree crystallographic restriction

`ExceptionalTraceSeed` showed the `E₇`/`E₈` seeds are the *traces* of the
order-`8`/order-`5` rotations (`trace(g₈)² = NT`,
`(2·trace(g₅)+1)² = NS+NT`).  This file proves the keystone that the
trace-mechanism narrative rested on, and explains *why these orders and
these surds*.

**The trace of an order-`n` rotation generates the real cyclotomic field
`ℚ(ζ_n)⁺ = ℚ(ζ_n + ζ_n⁻¹)`, of degree `φ(n)/2`** (`φ` = Euler totient,
the degree of `Φ_n`).  So the trace is:

  * **rational** (degree `1`) ⟺ `φ(n) ≤ 2` ⟺ `n ∈ {1,2,3,4,6}` — the
    classical *crystallographic restriction*: only these rotation orders
    have integer trace, hence sit in `GL(2,ℤ)`.  `E₆` (order `3`/`6`,
    trace `−1`/`1`) is here; its `√−3` is the discriminant, not the trace.
  * **quadratic** (degree `2`) for `n ∈ {5,8,10,12}` — the first orders
    *past* the crystallographic wall.  Their traces are real quadratic
    surds, and the two that anchor the exceptional rungs are
      - `n = 5`  (`E₈`): trace field `ℚ(√5)`, `√(NS+NT)`;
      - `n = 8`  (`E₇`): trace field `ℚ(√2)`, `√NT`.

**This is why `E₇`/`E₈` live one Cayley–Dickson doubling up.**  An
order-`n` rotation acts ℚ-irreducibly only in dimension `φ(n)`.  `φ(5) =
φ(8) = 4 = 2²` — the quaternion dimension.  So orders `5` and `8` are
*forbidden* in the 2D matrix layer (`φ > 2`) and first realised in the 4D
quaternion layer, exactly where `2I` and `2O` live.  `φ(NS+NT) = 4` is
the CD-rung dimension of the `E₈` rotation.

So the disc-mechanism and the trace-mechanism are one picture indexed by
`φ(n)`: `φ(n) ≤ 2` (rational trace, `E₆` in 2D, `√−3` on the
discriminant); `φ(n) = 4` (quadratic trace, `E₇`/`E₈` in 4D, seeds `√NT`
/ `√(NS+NT)` on the diagonal).  The surds `√2, √5` are not chosen — they
are the generators of the two degree-`2` real cyclotomic fields that
first appear when `φ` crosses `2`.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
open E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
open E213.Lib.Math.CayleyDickson.Tower.ExceptionalTraceSeed
open E213.Tactic.NatHelper (gcd213)

/-- Euler totient, defined purely by counting `gcd`-coprime residues
    (no Mathlib; `gcd213` is the repo's `∅`-axiom fuel-based gcd, since
    core `Nat.gcd`'s well-founded recursion leaks `propext`).
    `φ(n) = #{ k < n : gcd(k,n) = 1 }`. -/
def phi (n : Nat) : Nat := ((List.range n).filter (fun k => gcd213 k n == 1)).length

/-- The degree of the *real* cyclotomic field `ℚ(ζ_n)⁺` — the trace
    field of an order-`n` rotation (`= φ(n)/2` for `n ≥ 3`). -/
def traceFieldDegree (n : Nat) : Nat := phi n / 2

/-- **Crystallographic restriction (cyclotomic form).**  Over `1 ≤ n ≤
    12`, the rotation orders with *rational* trace (`φ(n) ≤ 2`) are
    exactly `{1,2,3,4,6}` — the classical crystallographic set.  These
    are the orders realisable in `GL(2,ℤ)`. -/
theorem crystallographic_restriction :
    (List.range 13).filter (fun n => 1 ≤ n && phi n ≤ 2) = [1, 2, 3, 4, 6] := by decide

/-- **The Cayley–Dickson lift.**  Allowing quadratic trace
    (`φ(n) ≤ 4`, i.e. trace-field degree `≤ 2`) adds exactly the
    exceptional orders `{5, 8, 10, 12}` to the crystallographic set —
    the orders that first appear in the 4D quaternion layer. -/
theorem cd_lift_orders :
    (List.range 13).filter (fun n => 1 ≤ n && phi n ≤ 4) = [1, 2, 3, 4, 5, 6, 8, 10, 12] := by
  decide

/-- The `E₆` orders `3`/`6` (and `4`) have **rational** trace
    (degree `1`): no quadratic seed on the diagonal. -/
theorem e6_trace_rational :
    traceFieldDegree 3 = 1 ∧ traceFieldDegree 4 = 1 ∧ traceFieldDegree 6 = 1 := by decide

/-- The `E₇`/`E₈` orders `8`/`5` have **quadratic** trace (degree `2`):
    real quadratic surds `√NT`/`√(NS+NT)` on the diagonal. -/
theorem e7_e8_trace_quadratic :
    traceFieldDegree 8 = 2 ∧ traceFieldDegree 5 = 2 := by decide

/-- The order-`(NS+NT)` rotation needs dimension `φ(NS+NT) = 4 = 2²` —
    the quaternion / 2nd-CD-rung dimension where `2I` lives.  Order `8`
    (`E₇`) likewise: `φ(8) = 4`. -/
theorem exceptional_rotation_dimension_four :
    phi (NS + NT) = 4 ∧ phi 8 = 4 ∧ (4 : Nat) = 2 * 2 := by decide

/-- ★★★ **Why `√2` and `√5`: the cyclotomic-degree picture, unified.**
    The trace of an order-`n` rotation generates `ℚ(ζ_n)⁺` of degree
    `φ(n)/2`.  Rational trace (`φ ≤ 2`) ⟺ orders `{1,2,3,4,6}` (the
    crystallographic set, `E₆` in 2D).  Quadratic trace first appears at
    orders `{5,8,10,12}` (dimension `φ = 4`, the quaternion layer); the
    two anchoring the exceptional rungs are order-`5` → `√(NS+NT)` (`E₈`)
    and order-`8` → `√NT` (`E₇`), matching the proven trace seeds.  The
    surds are forced, not chosen: they generate the two degree-`2` real
    cyclotomic fields immediately past `φ = 2`. -/
theorem why_root_two_and_root_five :
    -- crystallographic wall: rational-trace orders are exactly {1,2,3,4,6}.
    ((List.range 13).filter (fun n => 1 ≤ n && phi n ≤ 2) = [1, 2, 3, 4, 6])
    -- the exceptional rungs have quadratic trace, first at dimension φ = 4.
    ∧ (traceFieldDegree 5 = 2 ∧ traceFieldDegree 8 = 2)
    ∧ (phi 5 = 4 ∧ phi 8 = 4 ∧ phi (NS + NT) = 4)
    -- and those quadratic traces are the proven seeds √NT (n=8), √(NS+NT) (n=5).
    ∧ (octaTrace g8 * octaTrace g8 = (⟨(NT : Int), 0⟩ : ZRt2))
    ∧ ((⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩) * (⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩)
        = (⟨((NS : Int) + NT), 0⟩ : ZPhi)) :=
  ⟨crystallographic_restriction, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
   octahedral_trace_sq_eq_NT, icosian_trace_seed_eq_NS_NT⟩

end E213.Lib.Math.CayleyDickson.Tower.CyclotomicTraceDegree
