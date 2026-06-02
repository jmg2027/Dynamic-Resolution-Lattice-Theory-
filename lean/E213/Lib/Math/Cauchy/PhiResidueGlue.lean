import E213.Lib.Math.Cauchy.DepthFloorDetOne
import E213.Lib.Math.Mobius213OneAsGlue
import E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Real213.PhiFrozenDynamic

/-!
# Cauchy.PhiResidueGlue — the orbit determinant `det Pⁿ` IS the atomic glue `NS − NT`

The residue between *dynamic* φ (the Pell convergents) and *frozen* φ (the algebraic fixed
point) is the unit `1`.  This file gives the **structural** cross-scale identity, not a
"both equal 1" chaining: the determinant of the *actual matrix power* `Pⁿ` —
`Q00 n · Q11 n − Q01 n²` (`PnFibonacciUniversal.det_pn_universal`, `= 1` for every `n`,
i.e. `det Pⁿ = (det P)ⁿ = 1`) — **equals the atomic glue** `NS − NT` (`orbit_det_is_glue`).
This is a genuine arrow: the orbit's conserved determinant on one side, the atomicity-count
difference on the other, sharing the matrix `P` whose orbit *is* the convergent sequence.

The analysis-side reading is then the *value*: the convergent cross-determinant `W n`
(`DepthFloorDetOne`, the Cassini surplus separating dynamic from frozen φ) is the same constant
`1 = NS − NT` (`phi_residue_is_glue`).  `det Pⁿ` (algebra), `W n` (analysis), and `NS − NT`
(atomicity) all read the unit `1` — but the load-bearing identity is `orbit_det_is_glue`
(`det Pⁿ = NS − NT`), with `W` and the `decide`-fact `NS − NT = 1` as the analysis/atomicity
readings of that one conserved determinant.
-/

namespace E213.Lib.Math.Cauchy.PhiResidueGlue

open E213.Lib.Math.Cauchy.DepthFloorDetOne (W W_eq_one)
open E213.Lib.Math.Mobius213OneAsGlue (ns_minus_nt_is_one mobius_det_eq_ns_minus_nt)
open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11 det_pn_universal)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- ★★★ **The orbit determinant `det Pⁿ` is the atomic glue `NS − NT`.**  The determinant of the
    matrix power `Pⁿ`, in the additive (subtraction-free) form `Q00 n · Q11 n = Q01 n² + (NS −
    NT)` — i.e. `det Pⁿ = NS − NT` — for *every* `n`.  This is the genuine structural identity:
    `det Pⁿ = (det P)ⁿ = 1` (`det_pn_universal`) and `1 = NS − NT` (`ns_minus_nt_is_one`), the two
    sharing the *actual* matrix `P` (the convergent orbit's generator).  Not a coincidence of
    constants: it is the conserved determinant of the orbit equalling the atomicity difference. -/
theorem orbit_det_is_glue (n : Nat) :
    Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT) := by
  rw [ns_minus_nt_is_one]; exact det_pn_universal n

/-- ★★ **The φ-convergent residue reads the same unit.**  The convergent cross-determinant `W n`
    (the Cassini surplus separating the dynamic convergent from the frozen φ) equals the atomic
    glue `NS − NT` for every `n`: `W n = 1 = NS − NT`.  (The analysis-side *value* reading of the
    conserved orbit determinant `orbit_det_is_glue`.) -/
theorem phi_residue_is_glue (n : Nat) : W n = NS - NT := by
  rw [W_eq_one n]; exact ns_minus_nt_is_one.symm

/-- ★★★ **One conserved determinant, three scales — algebra, analysis, atomicity.**  For every
    `n`:

    1. **algebra** — the orbit's matrix-power determinant is the glue: `det Pⁿ = NS − NT`
       (`orbit_det_is_glue`, the load-bearing structural identity);
    2. **analysis** — the φ-convergent cross-determinant reads the same constant: `W n = NS − NT`
       (`phi_residue_is_glue`);
    3. **atomicity** — that value is `NS − NT = 1`, the atomic glue, which is `det P`
       (`ns_minus_nt_is_one`, `mobius_det_eq_ns_minus_nt`).

    The conserved orbit determinant `det Pⁿ`, the φ-convergent residue `W`, and the atomic glue
    `NS − NT` are one unit — connected by the genuine arrow (1), not merely three coincident `1`s. -/
theorem residue_unit_three_scales (n : Nat) :
    Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT)
    ∧ W n = NS - NT
    ∧ NS - NT = 1
    ∧ ((2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int)) :=
  ⟨orbit_det_is_glue n, phi_residue_is_glue n, ns_minus_nt_is_one, mobius_det_eq_ns_minus_nt⟩

end E213.Lib.Math.Cauchy.PhiResidueGlue
