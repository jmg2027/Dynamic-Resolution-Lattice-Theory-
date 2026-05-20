import E213.Lib.Math.Cohomology.Surfaces.T2Squared

/-!
# Cup-pairing on H²(T²×T²) — signature (3, 3)

Standard Hodge Index Theorem on the 4-fold T²×T² (real dim 4 =
complex dim 2) predicts signature
  (1 + 2·h^{2,0}, h^{1,1} − 1) = (1 + 2·1, 4 − 1) = (3, 3)
for the symmetric cup-pairing on H²(T²×T²; ℤ) ≅ ℤ⁶.

In the wedge basis `{a₁b₁, a₁a₂, a₁b₂, b₁a₂, b₁b₂, a₂b₂}` the
6×6 cup-pairing matrix is the **3-block hyperbolic form**:

  · `(a₁b₁) ⌣ (a₂b₂)` = +1   [block 1 — both T² volume forms]
  · `(a₁a₂) ⌣ (b₁b₂)` = −1   [block 2 — `a` × `b` in each factor]
  · `(a₁b₂) ⌣ (b₁a₂)` = +1   [block 3 — cross-edges]
  · all other off-diagonal entries 0
  · all diagonal entries 0

Each `[[0, ±1], [±1, 0]]` block has eigenvalues ±1, contributing
signature (1, 1).  Three blocks ⟹ total signature (3, 3).

This realises Hodge Index Theorem at the 4-fold level — the
**second** point in the conjectured `T²ⁿ` signature sequence:

  signature(H^n; T²ⁿ) = (½·C(2n, n), ½·C(2n, n))

  · n = 1 (T²):     (1, 1)   = (½·2, ½·2)
  · n = 2 (T²×T²):  (3, 3)   = (½·6, ½·6)   ← this commit
  · n = 3 (T²³):    (10, 10) predicted = (½·20, ½·20)

STRICT ∅-AXIOM (all by `decide` on the 6-cell enumeration).
-/

namespace E213.Lib.Math.Cohomology.Surfaces.T2Squared.HodgeIndex

open E213.Lib.Math.Cohomology.Surfaces.T2Squared

/-- Symmetric cup-pairing C² × C² → C⁴.

    From the wedge of two 2-forms to the unique 4-form `vol`.
    Coefficient of `vol` is `Σ ε(σ) · α(σ_lhs) · β(σ_rhs)` over
    the 3 disjoint pairs of 2-cells whose product is the volume:

      pair 1:  (a₁b₁ , a₂b₂)   with sign +1
      pair 2:  (a₁a₂ , b₁b₂)   with sign −1
      pair 3:  (a₁b₂ , b₁a₂)   with sign +1

    Symmetric: `cup α β = cup β α` (graded comm of two 2-forms,
    sign `(-1)^{2·2} = +1`). -/
def cup (α β : C2) : C4 := fun _ =>
  -- Block 1: a₁b₁ × a₂b₂  (sign +)
    α Cell2.a1b1 * β Cell2.a2b2 + α Cell2.a2b2 * β Cell2.a1b1
  -- Block 2: a₁a₂ × b₁b₂  (sign −)
  - α Cell2.a1a2 * β Cell2.b1b2 - α Cell2.b1b2 * β Cell2.a1a2
  -- Block 3: a₁b₂ × b₁a₂  (sign +)
  + α Cell2.a1b2 * β Cell2.b1a2 + α Cell2.b1a2 * β Cell2.a1b2



/-! ## §1 — Standard basis of `C2` -/

/-- Six standard basis vectors of `C2`, one per Cell2 generator. -/
def basis_a1b1 : C2 := fun
  | Cell2.a1b1 => 1 | _ => 0
def basis_a1a2 : C2 := fun
  | Cell2.a1a2 => 1 | _ => 0
def basis_a1b2 : C2 := fun
  | Cell2.a1b2 => 1 | _ => 0
def basis_b1a2 : C2 := fun
  | Cell2.b1a2 => 1 | _ => 0
def basis_b1b2 : C2 := fun
  | Cell2.b1b2 => 1 | _ => 0
def basis_a2b2 : C2 := fun
  | Cell2.a2b2 => 1 | _ => 0

/-! ## §2 — The three hyperbolic blocks (sign ±1 cup-pairing) -/

theorem block1_pos : cup basis_a1b1 basis_a2b2 Cell4.vol = 1 := by decide
theorem block2_neg : cup basis_a1a2 basis_b1b2 Cell4.vol = -1 := by decide
theorem block3_pos : cup basis_a1b2 basis_b1a2 Cell4.vol = 1 := by decide

/-- Diagonals all zero (each generator has zero self-cup). -/
theorem diag_a1b1_zero : cup basis_a1b1 basis_a1b1 Cell4.vol = 0 := by decide
theorem diag_a1a2_zero : cup basis_a1a2 basis_a1a2 Cell4.vol = 0 := by decide
theorem diag_a1b2_zero : cup basis_a1b2 basis_a1b2 Cell4.vol = 0 := by decide
theorem diag_b1a2_zero : cup basis_b1a2 basis_b1a2 Cell4.vol = 0 := by decide
theorem diag_b1b2_zero : cup basis_b1b2 basis_b1b2 Cell4.vol = 0 := by decide
theorem diag_a2b2_zero : cup basis_a2b2 basis_a2b2 Cell4.vol = 0 := by decide

/-! ## §3 — Diagonalised basis: 3 positive + 3 negative classes

  `α₊_i := basis_pair_lhs + basis_pair_rhs`     →  cup(α₊, α₊) = +2
  `α₋_i := basis_pair_lhs − basis_pair_rhs`     →  cup(α₋, α₋) = −2  (block 1)
  (block 2 has opposite block sign, so the diagonal swaps)
-/

/-- Block-1 positive class: `a₁b₁ + a₂b₂` (Kähler-like). -/
def alpha1_plus : C2 := fun
  | Cell2.a1b1 => 1 | Cell2.a2b2 => 1 | _ => 0

/-- Block-1 negative class: `a₁b₁ − a₂b₂`. -/
def alpha1_minus : C2 := fun
  | Cell2.a1b1 => 1 | Cell2.a2b2 => -1 | _ => 0

/-- Block-3 positive class: `a₁b₂ + b₁a₂`. -/
def alpha3_plus : C2 := fun
  | Cell2.a1b2 => 1 | Cell2.b1a2 => 1 | _ => 0

/-- Block-3 negative class: `a₁b₂ − b₁a₂`. -/
def alpha3_minus : C2 := fun
  | Cell2.a1b2 => 1 | Cell2.b1a2 => -1 | _ => 0

/-- Block-2 (sign −) positive class: `a₁a₂ − b₁b₂` (note the sign
    flip — block 2's pairing is `−1` so `(a − b)·(a − b) = +2`). -/
def alpha2_plus : C2 := fun
  | Cell2.a1a2 => 1 | Cell2.b1b2 => -1 | _ => 0

/-- Block-2 negative class: `a₁a₂ + b₁b₂`. -/
def alpha2_minus : C2 := fun
  | Cell2.a1a2 => 1 | Cell2.b1b2 => 1 | _ => 0

/-! ## §4 — Three positive eigenvalues: `cup(α_i₊, α_i₊) = +2` -/

theorem cup_alpha1_plus : cup alpha1_plus alpha1_plus Cell4.vol = 2 := by decide
theorem cup_alpha2_plus : cup alpha2_plus alpha2_plus Cell4.vol = 2 := by decide
theorem cup_alpha3_plus : cup alpha3_plus alpha3_plus Cell4.vol = 2 := by decide

/-! ## §5 — Three negative eigenvalues: `cup(α_i₋, α_i₋) = −2` -/

theorem cup_alpha1_minus : cup alpha1_minus alpha1_minus Cell4.vol = -2 := by decide
theorem cup_alpha2_minus : cup alpha2_minus alpha2_minus Cell4.vol = -2 := by decide
theorem cup_alpha3_minus : cup alpha3_minus alpha3_minus Cell4.vol = -2 := by decide

end E213.Lib.Math.Cohomology.Surfaces.T2Squared.HodgeIndex
