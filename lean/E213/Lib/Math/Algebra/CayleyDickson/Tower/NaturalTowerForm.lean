import E213.Lib.Math.Algebra.CayleyDickson.Tower.UnitResidueRootTwo
import E213.Meta.Nat.IntHelpers

/-!
# Building over `ℕ`: the `√D` are shadows; the recurrence is the exact form

Question (parallel branch): the seeds keep coming out as *roots*
(`ℤ[√2]`, `ℤ[√5]`) — is that an artifact of viewing things over `ℤ`?
Built over `ℕ`, is there a *more accurate* form?

**Yes.**  The `√D` are the `ℝ`-diagonalisation (Binet / eigenvalue)
shadows of pure-`ℕ` recurrences whose coefficients and seeds are the
atomic `{NS, NT}`.  Over `ℕ` the surds dissolve.

## `√D` is the residue of non-squareness over `ℕ`

A `√D` is a *root* exactly when `D` is **not** a perfect square in `ℕ`:
the radicand lies strictly between consecutive squares, so no `ℕ`/`ℤ`
value squares to it — the surd is the *residue* of the failed square
root.

  `NT = 2`:    `1² < 2 < 2²`   (between `1,4`)  — non-square.
  `NS+NT = 5`: `2² < 5 < 3²`   (between `4,9`)  — non-square.
  `−NS = −3`:  `m² ≥ 0 > −3` for every `m`      — no real root at all.

## The exact `ℕ` form: a recurrence with atomic coefficients

The `E₈` seed `√(NS+NT) = √5` is, over `ℕ`, the **Lucas recurrence**

  `L₀ = NT,  L₁ = NS,  L_{n+1} = NS · L_n − L_{n−1}`   →   `2,3,7,18,47,…`

— pure `ℕ`, *no* `√5`.  Its coefficient is `NS = trace P` and its seeds
are `{NT, NS}`; it is exactly `trace Pⁿ` (the Möbius `P = [[2,1],[1,1]]`),
and `√5` appears only when `P` is diagonalised over `ℝ` (eigenvalues
`φ², φ⁻²`, `L_n = φ^{2n} + φ^{−2n}`).  The recurrence is the finitary
exact object; the surd is the closed-form (Binet) shadow.

Likewise the `E₇` seed `√NT = √2` is, over `ℕ`/`ℤ`, the doubling map
`D(x) = x² − NT` (`TraceDoublingMap`): the integer-sequence form, surd-free.

So building over `ℕ` *is* more accurate: the exceptional structure is the
integer matrix `P` and the finite groups `2T,2O,2I` — pure counting
objects — and the `√D` are their `ℝ`-trace shadows, residues of the
square root that `ℕ` does not contain.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.NaturalTowerForm

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.Algebra.CayleyDickson.Tower.UnitResidueRootTwo

/-- **The seeds are residues of non-squareness over `ℕ`.**  Each positive
    radicand lies strictly between consecutive squares (so is no perfect
    square); `−NS < 0 ≤ m²` for every `m` (no real root). -/
theorem seeds_are_nonsquare_residues :
    -- NT = 2 between 1², 2²
    ((1 * 1 < NT) ∧ (NT < 2 * 2))
    -- NS+NT = 5 between 2², 3²
    ∧ ((2 * 2 < NS + NT) ∧ (NS + NT < 3 * 3))
    -- −NS: every square is ≥ 0, so never −NS
    ∧ (∀ m : Int, 0 ≤ m * m) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  exact fun m => E213.Meta.Nat.IntHelpers.mul_self_nonneg m

/-- The Lucas recurrence: `L₀ = NT`, `L₁ = NS`, `L_{n+1} = NS·L_n −
    L_{n−1}` (pure `ℕ`). -/
def Lr : Nat → Nat
  | 0     => NT
  | 1     => NS
  | n + 2 => NS * Lr (n + 1) - Lr n

/-- `2×2` `ℕ`-matrix product, and `Pⁿ`, `P = [[2,1],[1,1]]`. -/
def mm (x y : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
   x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)
def Pn : Nat → Nat × Nat × Nat × Nat
  | 0     => (1, 0, 0, 1)
  | n + 1 => mm (Pn n) (2, 1, 1, 1)

/-- **The `ℕ`-native form of `√(NS+NT)`: the Lucas recurrence.**  Pure
    `ℕ` values `2,3,7,18,47`, coefficient `NS`, seeds `{NT, NS}`; no
    `√5`. -/
theorem lucas_recurrence_natural_form :
    (Lr 0, Lr 1, Lr 2, Lr 3, Lr 4) = (NT, NS, 7, 18, 47)
    ∧ (Lr 0 = NT ∧ Lr 1 = NS) := by decide

/-- **The recurrence is `trace Pⁿ`.**  `√5` is only the `ℝ`-eigenvalue
    shadow; over `ℕ` the exact object is `trace Pⁿ = L_n`. -/
theorem lucas_is_trace_P_pow :
    ((Pn 2).1 + (Pn 2).2.2.2 = Lr 2)
    ∧ ((Pn 3).1 + (Pn 3).2.2.2 = Lr 3)
    ∧ ((Pn 4).1 + (Pn 4).2.2.2 = Lr 4) := by decide

/-- ★★★ **Over `ℕ` the surds dissolve into recurrences.**  Each seed
    `√D` is the residue of a non-square `D` (between consecutive squares,
    or negative); its exact `ℕ` form is a recurrence with atomic
    coefficients `{NS, NT}`: `√(NS+NT)` is the Lucas recurrence `L_{n+1} =
    NS·L_n − L_{n−1}` (`L₀=NT, L₁=NS`) `= trace Pⁿ`, surd-free.  The `√D`
    is the `ℝ`-diagonalisation shadow of the integer matrix `P`; the
    recurrence is the more accurate, finitary form. -/
theorem natural_tower_form :
    -- the seeds are non-square residues.
    ((1 * 1 < NT ∧ NT < 2 * 2) ∧ (2 * 2 < NS + NT ∧ NS + NT < 3 * 3))
    -- the ℕ-native form: Lucas recurrence, atomic coefficients, no √.
    ∧ ((Lr 0 = NT ∧ Lr 1 = NS) ∧ (Lr 2, Lr 3, Lr 4) = (7, 18, 47))
    -- = trace Pⁿ (the integer matrix; √5 only in the eigenvalues).
    ∧ ((Pn 3).1 + (Pn 3).2.2.2 = Lr 3 ∧ (Pn 4).1 + (Pn 4).2.2.2 = Lr 4) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Algebra.CayleyDickson.Tower.NaturalTowerForm
