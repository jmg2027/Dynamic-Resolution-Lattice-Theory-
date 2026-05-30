import E213.Lib.Math.Real213.Core.ValidCut
import E213.Lib.Math.Real213.PhiConvergence

/-!
# PhiAsCut — φ as a single ValidCut, directly (no Cauchy completion)

`PhiConvergence` pins φ as the unique nested-bracket limit of the Pell
convergents, but as a *sequence* of rational brackets.  The remaining step —
φ as one `ValidCut` object — turns out **not** to need Cauchy-completion
infrastructure: φ has a closed-form decidable cut.

A `ValidCut c` is an upper rational set: `c m k = true` means `m/k ≥` the value.
For φ = (1+√5)/2 (the positive root of `x² = x + 1`):

    m/k ≥ φ  ⟺  2m ≥ k  ∧  (2m − k)² ≥ 5k²

(from `(2·(m/k) − 1)² ≥ 5`, i.e. `(2m − k)² ≥ 5k²`, with the sign guard
`2m ≥ k` so the Nat subtraction is faithful).  This is a single decidable
predicate, so `phiCut` is a concrete `Nat → Nat → Bool`, and it is a `ValidCut`:
both monotonicities are direct Nat arithmetic.

So the limit-ratio reading is now **φ as one Cut object**, closing the last
deferred step — the residue's irrational signature is a single 213-native Cut,
built with no completion machinery.
-/

namespace E213.Lib.Math.Real213.PhiAsCut

open E213.Lib.Math.Real213.Core.ValidCut (ValidCut)

/-- **φ as a single cut**: `m/k ≥ φ ⟺ 2m ≥ k ∧ (2m − k)² ≥ 5k²`.
    The closed-form decidable cut for the golden ratio.  (One `decide` over the
    conjunction — not `&&` of two — to keep proofs propext-free.) -/
def phiCut (m k : Nat) : Bool :=
  decide (k ≤ 2 * m ∧ 5 * k * k ≤ (2 * m - k) * (2 * m - k))

/-- `phiCut` agrees with the Pell convergents: `8/5 < φ` (false), `5/3 > φ`
    (true), `13/8 > φ` (true), `21/13 < φ` (false) — the alternating bracket. -/
theorem phiCut_brackets :
    phiCut 8 5 = false ∧ phiCut 5 3 = true
    ∧ phiCut 13 8 = true ∧ phiCut 21 13 = false
    ∧ phiCut 2 1 = true ∧ phiCut 1 1 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`upM`**: increasing the numerator keeps `m/k ≥ φ` (a larger upper rational
    stays above φ).  Direct: `m₁ ≤ m₂` makes `2m − k` larger, and squaring is
    monotone. -/
theorem phiCut_upM (m1 m2 k : Nat) (hm : m1 ≤ m2)
    (h : phiCut m1 k = true) : phiCut m2 k = true := by
  unfold phiCut at h ⊢
  obtain ⟨hk1, hsq1⟩ := of_decide_eq_true h
  have hk2 : k ≤ 2 * m2 := Nat.le_trans hk1 (Nat.mul_le_mul_left 2 hm)
  apply decide_eq_true
  refine ⟨hk2, ?_⟩
  have hsub : 2 * m1 - k ≤ 2 * m2 - k :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hm) k
  exact Nat.le_trans hsq1 (Nat.mul_le_mul hsub hsub)

/-- **`dnK`**: decreasing the denominator keeps `m/k ≥ φ` (the rational grows).
    Direct: `k₁ ≤ k₂` shrinks `5k²` and grows `(2m − k)²`. -/
theorem phiCut_dnK (m k1 k2 : Nat) (hk : k1 ≤ k2)
    (h : phiCut m k2 = true) : phiCut m k1 = true := by
  unfold phiCut at h ⊢
  obtain ⟨hk2le, hsq2⟩ := of_decide_eq_true h
  have hk1le : k1 ≤ 2 * m := Nat.le_trans hk hk2le
  apply decide_eq_true
  refine ⟨hk1le, ?_⟩
  have hleft : 5 * k1 * k1 ≤ 5 * k2 * k2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 5 hk) hk
  have hsub : 2 * m - k2 ≤ 2 * m - k1 :=
    E213.Tactic.NatHelper.sub_le_sub_left (2 * m) hk
  have hright : (2 * m - k2) * (2 * m - k2) ≤ (2 * m - k1) * (2 * m - k1) :=
    Nat.mul_le_mul hsub hsub
  exact Nat.le_trans hleft (Nat.le_trans hsq2 hright)

/-- ★★★ **φ is a single `ValidCut`.**  The golden ratio is a concrete 213-native
    Cut object — a decidable upper rational set with both monotonicities — built
    directly from `x² = x + 1`, with no Cauchy-completion infrastructure.  This
    closes the last deferred step: the residue's irrational limit-ratio
    signature is one Cut, not just a nested bracket sequence. -/
theorem phiCut_valid : ValidCut phiCut where
  upM := phiCut_upM
  dnK := phiCut_dnK

end E213.Lib.Math.Real213.PhiAsCut
