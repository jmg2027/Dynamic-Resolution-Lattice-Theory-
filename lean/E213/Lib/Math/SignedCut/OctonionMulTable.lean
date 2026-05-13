import E213.Lib.Math.SignedCut.OctonionMulRule
import E213.Lib.Math.SignedCut.QuaternionMulTable

/-!
# Octonion partial multiplication table (∅-axiom)

Octonion basis: `1, e₁, e₂, …, e₇` (8-dim).  Products determined
by **Fano plane** structure (7 oriented triples).

213-native paradigm: octonion = level-3 nested pair `Oct := Quat
× Quat`.  Identity = `(quatOne, quatZero)`; basis e_k decomposes
into the level-2 quaternion components either as `(quatX,
quatZero)` (k ≤ 3, "real" half) or `(quatZero, quatX)` (k ≥ 4,
"imaginary" half).

Atomic content: structural distinctness of the basis elements
e₀ (= identity), e₁, e₂, e₃ at the level-2 component level.
-/

namespace E213.Lib.Math.SignedCut.OctonionMulTable

open E213.Lib.Math.SignedCut.OctonionMulRule (Oct octOne quatZero)
open E213.Lib.Math.SignedCut.QuaternionMulRule
  (Quat quatOne quatI quatJ quatK)
open E213.Lib.Math.SignedCut.QuaternionMulTable
  (cuts_distinct_at_0_1 quatI_neq_quatJ)

/-- e₁ basis octonion: `(quatI, quatZero)` (i in real half). -/
def octE1 : Oct := (quatI, quatZero)

/-- e₂ basis octonion: `(quatJ, quatZero)`. -/
def octE2 : Oct := (quatJ, quatZero)

/-- e₃ basis octonion: `(quatK, quatZero)`. -/
def octE3 : Oct := (quatK, quatZero)

/-- e₄ basis octonion: `(quatZero, quatOne)` (in imaginary half). -/
def octE4 : Oct := (quatZero, quatOne)

/-- ★ e₁ first quaternion = quatI. -/
theorem octE1_first : octE1.1 = quatI := rfl

/-- ★ e₂ first quaternion = quatJ. -/
theorem octE2_first : octE2.1 = quatJ := rfl

/-- ★ e₁ ≠ e₂ via inherited quaternion distinctness. -/
theorem octE1_neq_octE2 : octE1 ≠ octE2 := by
  intro h
  have h1 : octE1.1 = octE2.1 := by rw [h]
  rw [octE1_first, octE2_first] at h1
  exact quatI_neq_quatJ h1

/-- ★ Octonion identity ≠ e₄ — identity has `quatOne` first,
    e₄ has `quatZero` first. -/
theorem octOne_neq_octE4 : octOne ≠ octE4 := by
  intro h
  have h1 : octOne.1 = octE4.1 := by rw [h]
  have hone : octOne.1 = quatOne := rfl
  have he4 : octE4.1 = quatZero := rfl
  rw [hone, he4] at h1
  -- quatOne ≠ quatZero via component (1,1) check
  have h2 : quatOne.1.1 = quatZero.1.1 := by rw [h1]
  have hone2 : quatOne.1.1 = E213.Lib.Math.Real213.Sum.CutSumTest.constCut 1 1
              := rfl
  have hzero2 : quatZero.1.1 = E213.Lib.Math.Real213.Sum.CutSumTest.constCut 0 1
              := rfl
  rw [hone2, hzero2] at h2
  have hpt : (E213.Lib.Math.Real213.Sum.CutSumTest.constCut 1 1
              : Nat → Nat → Bool) 0 1
           = (E213.Lib.Math.Real213.Sum.CutSumTest.constCut 0 1
              : Nat → Nat → Bool) 0 1 := by rw [h2]
  have ⟨e1, e2⟩ := cuts_distinct_at_0_1
  rw [e1, e2] at hpt
  exact Bool.noConfusion hpt

end E213.Lib.Math.SignedCut.OctonionMulTable
