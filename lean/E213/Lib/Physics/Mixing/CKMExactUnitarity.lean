import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIAlgebra213

/-!
# CKMExactUnitarity — the `ℤ[i]` CKM at `δ = 90°` is exactly unitary, maximal CP (item a)

The numerical evaluation of the cohomological Yukawa (`CohomologicalYukawaEval` item a),
ported into ∅-axiom Lean — the float-free `ℤ[i]` check the rust `ckm_cp_phase` performs.

The cohomological cup–Hodge pairing is diagonal (`h = I`), so it supplies the **phase**
(`J = i`, `δ = 90°`, the signed Hodge `⋆²=−1`) and the **index**, while the **mixing angles**
are the separate DRLT atomic rationals (`CohomologicalYukawaEval`).  Assembling the full CKM in
the standard PDG parametrisation at `δ = 90°` (`e^{∓iδ} = ∓i`, the `ℤ[i]` unit) with **rational
(Pythagorean-triple) mixing angles** `θ₁₂=(3,4,5)`, `θ₁₃=(5,12,13)`, `θ₂₃=(8,15,17)`, scaled by
`D = 5·13·17 = 1105` to clear denominators, makes **every entry a Gaussian integer** `a + b·i`.
The whole verification is then exact `ZI` arithmetic — no floats, no approximation.

  * `ckm_unitary` — `M·M† = D²·I` exactly (`D² = 1221025`).
  * `ckm_apex_pure_imaginary` — `M_ub = −425·i` is **pure imaginary** (`Re = 0`): the down-sector
    `J = i`, `δ = 90°`.
  * `ckm_cp_maximal` — the Jarlskog `Im(V_us V_cb V_ub* V_cs*) ≠ 0`: CP violated, maximal at the
    `δ = 90°` apex.

So the `ℤ[i]` (signed-Hodge `⋆`) complex structure yields, **exactly**, a unitary CKM with
`δ = 90°` and maximal CP — the ∅-axiom confirmation of `Mixing/CPMaximalPhase` /
`CohomologicalYukawaEval`.  All theorems PURE.
-/

namespace E213.Lib.Physics.Mixing.CKMExactUnitarity

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI (conj)

/-! ## §1 — the scaled CKM `M = D·V` over the Gaussian integers (`D = 1105`) -/

/-- The scaled CKM at `δ = 90°`, every entry a Gaussian integer (`= D·V`, `D = 1105`).
    Row/col `(0,1,2) = (u,c,t)/(d,s,b)`; the apex `M_ub = ⟨0,−425⟩ = −425·i`. -/
def m00 : ZI := ⟨816, 0⟩
def m01 : ZI := ⟨612, 0⟩
def m02 : ZI := ⟨0, -425⟩
def m10 : ZI := ⟨-585, -160⟩
def m11 : ZI := ⟨780, -120⟩
def m12 : ZI := ⟨480, 0⟩
def m20 : ZI := ⟨312, -300⟩
def m21 : ZI := ⟨-416, -225⟩
def m22 : ZI := ⟨900, 0⟩

/-- The `(i,j)` entry of `M·M†`: `row_i · conj(row_j) = Σ_k M i k · conj (M j k)`. -/
def rowdot (a0 a1 a2 b0 b1 b2 : ZI) : ZI :=
  a0 * conj b0 + a1 * conj b1 + a2 * conj b2

/-! ## §2 — exact unitarity `M·M† = D²·I` -/

/-- ★★★★★ **Exact unitarity.**  `M·M† = D²·I` over `ℤ[i]` (`D² = 1105² = 1221025`): the three
    diagonal entries are `⟨1221025,0⟩` and all six off-diagonal entries vanish.  A genuine
    unitary CKM, float-free. -/
theorem ckm_unitary :
    -- diagonal = D² = 1221025
    (rowdot m00 m01 m02 m00 m01 m02 = ⟨1221025, 0⟩
      ∧ rowdot m10 m11 m12 m10 m11 m12 = ⟨1221025, 0⟩
      ∧ rowdot m20 m21 m22 m20 m21 m22 = ⟨1221025, 0⟩)
    -- off-diagonal = 0
    ∧ (rowdot m00 m01 m02 m10 m11 m12 = ⟨0, 0⟩
      ∧ rowdot m00 m01 m02 m20 m21 m22 = ⟨0, 0⟩
      ∧ rowdot m10 m11 m12 m20 m21 m22 = ⟨0, 0⟩
      ∧ rowdot m10 m11 m12 m00 m01 m02 = ⟨0, 0⟩
      ∧ rowdot m20 m21 m22 m00 m01 m02 = ⟨0, 0⟩
      ∧ rowdot m20 m21 m22 m10 m11 m12 = ⟨0, 0⟩) := by decide

/-! ## §3 — the apex is pure imaginary (`δ = 90°`) and CP is maximal -/

/-- ★★★★ **The apex carries the `i`.**  `M_ub = ⟨0,−425⟩ = −425·i` is pure imaginary
    (`Re = 0`) — the down-sector complex structure `J = i`, the phase `δ = arg(i) = 90°`. -/
theorem ckm_apex_pure_imaginary : m02 = ⟨0, -425⟩ ∧ m02.re = 0 := by decide

/-- The (scaled) Jarlskog product `V_us · V_cb · V_ub* · V_cs*`. -/
def jprod : ZI := m01 * m12 * conj m02 * conj m11

/-- ★★★★ **CP violated, maximal.**  The Jarlskog invariant `Im(V_us V_cb V_ub* V_cs*) ≠ 0`
    (scaled value `97381440000`), nonzero ⇒ CP is violated; with the pure-imaginary apex it is
    the maximal `sin δ = 1`, `δ = 90°`. -/
theorem ckm_cp_maximal : jprod.im = 97381440000 ∧ jprod.im ≠ 0 := by decide

/-! ## §4 — capstone (item a, closed) -/

/-- ★★★★★★ **The cohomological CKM is exactly unitary with `δ = 90°`, maximal CP.**
    Assembling the cohomological phase (`J = i`, `δ = 90°`) with the DRLT mixing angles
    (Pythagorean-triple rationals, scaled by `D = 1105`) gives a `ℤ[i]` CKM that is exactly
    unitary (`M·M† = D²·I`), pure-imaginary at the apex (`M_ub = −425·i`, `δ = 90°`), and
    maximally CP-violating (Jarlskog `≠ 0`).  Item (a) of `theory/physics/cp_phase.md` —
    the float-free confirmation of `Mixing/CPMaximalPhase`. -/
theorem ckm_cp_phase_exact :
    -- unitary: M·M† = D²·I (diagonal D², off-diagonal 0)
    rowdot m00 m01 m02 m00 m01 m02 = ⟨1221025, 0⟩
    ∧ rowdot m00 m01 m02 m10 m11 m12 = ⟨0, 0⟩
    -- apex pure imaginary: δ = 90°
    ∧ m02.re = 0
    -- CP violated (Jarlskog ≠ 0), maximal at the i-apex
    ∧ jprod.im ≠ 0 := by decide

end E213.Lib.Physics.Mixing.CKMExactUnitarity
