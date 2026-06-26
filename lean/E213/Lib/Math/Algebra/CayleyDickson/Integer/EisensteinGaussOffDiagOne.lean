import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinShiftTerm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInvPerm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero

/-!
# The cubic Gauss-sum off-diagonal coefficient is `−1` (∅-axiom)

The `e_k`-coefficient (`0<k<p`) of `g·conj g` in the free group ring `R[C_p]`:

  `(g ⋆ conj g)(k) = ofInt (−1)`   (`gauss_conj_offdiag`).

Assembled from the one-sided shift form `Σ_{j<p} χ_ω((j+k)%p)·χ̄_ω(j)` (`gauss_offdiag_shift`):
drop the `j=0` term (`listSum_rangeList_split`, `χ̄_ω(0)=0`); rewrite each unit term to
`χ_ω(1+k·j⁻¹)` (`chiOmega_shift_term`); reindex by inversion (`totativeList_inv_lperm`) then
multiplication-by-`k` (`lperm_image`) — both clean unit-permutations — to the `k`-independent
`C = Σ_{z∈tot} χ_ω((1+z)%p)`; and evaluate `C` by the additive-shift permutation `z↦(z+1)%p`
(`rangeList_add_lperm`) + the unit-sum split + cubic-character orthogonality
(`chiListSum_totatives_zero`): `χ_ω(1) + C = Σ_{[0,p)} χ_ω = 0`, so `C = −χ_ω(1) = ofInt(−1)`.

With the diagonal `(g⋆ḡ)(0)=↑(p−1)` (`gauss_conj_zero`), this is `g·conj g = p·1 − N`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharDiv (chiOmega_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_add ofInt_neg)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj gauss_conj_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift (gauss_offdiag_shift)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinShiftTerm (chiOmega_shift_term)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeTotatives
  (mem_totativeList_prime listSum_rangeList_split)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_congr listSum_map listSum_lperm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
  (sumRange_eq_listSum rangeList_add_lperm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInvPerm (totativeList_inv_lperm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero
  (chiListSum chiListSum_totatives_zero)
open E213.Lib.Math.Combinatorics.RangeList (rangeList)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_pos totativeList_le totativeList_coprime totative_lt_n lperm_image aInv)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Meta.Algebra213.Ring213 (zero_add add_zero add_assoc neg_add_cancel_self mul_zero)

/-- `listSum (chiOmega p m x) L = chiListSum p m x L` — the generic list sum of the character is the
    bespoke `chiListSum`.  Trivial structural induction. -/
private theorem listSum_chiOmega (p m x : Nat) :
    ∀ L : List Nat, listSum (chiOmega p m x) L = chiListSum p m x L
  | [] => rfl
  | t :: l => by
      show chiOmega p m x t + listSum (chiOmega p m x) l = chiOmega p m x t + chiListSum p m x l
      rw [listSum_chiOmega p m x l]

/-- **`Σ_{z∈tot} χ_ω((1+z)%p) = ofInt(−1)`** — the `k`-independent off-diagonal constant `C`.
    Add-shift `z↦(z+1)%p` permutes `[0,p)`, so `Σ_{[0,p)} χ_ω((1+z)%p) = Σ_{[0,p)} χ_ω = 0`
    (character orthogonality); splitting off `z=0` (value `χ_ω(1)=ofInt 1`) leaves `C = −ofInt 1`.
    ∅-axiom. -/
theorem offdiag_const {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p) = ofInt (-1) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  -- Rs 0 = χ_ω(1) = ofInt 1
  have hRs0 : chiOmega p m x ((1 + 0) % p) = ofInt 1 := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt hp]; exact chiOmega_one hp
  -- split the full [0,p) sum of Rs
  have hsplitR : listSum (fun z => chiOmega p m x ((1 + z) % p)) (rangeList p)
      = chiOmega p m x ((1 + 0) % p)
        + listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p) :=
    listSum_rangeList_split (fun z => chiOmega p m x ((1 + z) % p)) hp hpr
  -- the full [0,p) sum of Rs equals the full sum of χ_ω (add-shift reindex)
  have hbeta : listSum (fun z => chiOmega p m x ((1 + z) % p)) (rangeList p)
      = listSum (chiOmega p m x) (rangeList p) := by
    calc listSum (fun z => chiOmega p m x ((1 + z) % p)) (rangeList p)
        = listSum (fun z => chiOmega p m x ((z + 1) % p)) (rangeList p) :=
          listSum_congr (rangeList p) (fun z _ => by rw [Nat.add_comm 1 z])
      _ = listSum (chiOmega p m x) ((rangeList p).map (fun z => (z + 1) % p)) :=
          (listSum_map (chiOmega p m x) (fun z => (z + 1) % p) (rangeList p)).symm
      _ = listSum (chiOmega p m x) (rangeList p) :=
          (listSum_lperm (chiOmega p m x) (rangeList_add_lperm hppos (Nat.le_of_lt hp))).symm
  -- the full sum of χ_ω is 0 (drop z=0, orthogonality)
  have hchi0 : listSum (chiOmega p m x) (rangeList p) = 0 := by
    have hsplitC : listSum (chiOmega p m x) (rangeList p)
        = chiOmega p m x 0 + listSum (chiOmega p m x) (totativeList p) :=
      listSum_rangeList_split (chiOmega p m x) hp hpr
    rw [hsplitC, chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩, zero_add, listSum_chiOmega p m x,
        chiListSum_totatives_zero hp hp3 hpr h3m hm1 hdn hω hx]
  -- assemble:  ofInt 1 + C = 0  ⟹  C = ofInt(−1)
  have hzeroEq : ofInt 1 + listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p) = 0 := by
    rw [← hRs0, ← hsplitR, hbeta, hchi0]
  calc listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p)
      = 0 + listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p) := (zero_add _).symm
    _ = (-(ofInt 1) + ofInt 1) + listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p) := by
          rw [neg_add_cancel_self]
    _ = -(ofInt 1) + (ofInt 1 + listSum (fun z => chiOmega p m x ((1 + z) % p)) (totativeList p)) :=
          add_assoc _ _ _
    _ = -(ofInt 1) + 0 := by rw [hzeroEq]
    _ = -(ofInt 1) := add_zero _
    _ = ofInt (-1) := (ofInt_neg 1).symm

/-- ★★★★★ **The off-diagonal coefficient `(g⋆ḡ)(k) = −1`** for `0<k<p`.  The shift form reduces
    (drop `j=0`, per-term `χ((j+k)/j)=χ(1+k/j)`, inversion + mult reindex) to the `k`-independent
    constant `C = ofInt(−1)` (`offdiag_const`).  With `(g⋆ḡ)(0)=↑(p−1)`, this is `g·ḡ = p·1 − N`.
    ∅-axiom. -/
theorem gauss_conj_offdiag {d : ZOmega} {p m x k : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hk0 : 0 < k) (hkp : k < p) :
    conv p (gauss p m x) (gaussConj p m x) k = ofInt (-1) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hkgcd : gcd213 k p = 1 := totativeList_coprime ((mem_totativeList_prime hp hpr).mpr ⟨hk0, hkp⟩)
  rw [gauss_offdiag_shift hk0 hkp, sumRange_eq_listSum,
      listSum_rangeList_split (fun j => chiOmega p m x ((j + k) % p) * conj (chiOmega p m x j)) hp hpr]
  -- the j=0 term vanishes (χ̄_ω(0)=0)
  rw [show chiOmega p m x ((0 + k) % p) * conj (chiOmega p m x 0) = 0 by
        rw [chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩,
            show conj (0 : ZOmega) = 0 from rfl, mul_zero], zero_add]
  -- per-term:  χ((j+k)/j) = χ(1+k/j)
  rw [listSum_congr (totativeList p) (fun j hj =>
        chiOmega_shift_term hp hp3 hpr h3m hdn hω hx hk0 hkp (totativeList_pos hj)
          (totative_lt_n hp (totativeList_coprime hj) (totativeList_pos hj) (totativeList_le hj))
          (totativeList_coprime hj))]
  -- reindex: inversion (j ↦ j⁻¹) then multiplication (v ↦ k·v)
  rw [(listSum_map (fun v => chiOmega p m x ((1 + (k * v) % p) % p))
        (fun j => aInv j p % p) (totativeList p)).symm,
      (listSum_lperm (fun v => chiOmega p m x ((1 + (k * v) % p) % p))
        (totativeList_inv_lperm hp)).symm,
      (listSum_map (fun z => chiOmega p m x ((1 + z) % p))
        (fun v => (k * v) % p) (totativeList p)).symm,
      (listSum_lperm (fun z => chiOmega p m x ((1 + z) % p))
        (lperm_image hp hkgcd)).symm]
  exact offdiag_const hp hp3 hpr h3m hm1 hdn hω hx

/-- ★★★★★ **The Gauss-sum norm `g·conj g = p·1 − N`** (coefficient form) — for every `k < p`,

  `(g ⋆ conj g)(k) = ofInt(p−1)` if `k = 0`,  `ofInt(−1)` otherwise.

  The `e_0`-coefficient `p−1` (`gauss_conj_zero`, the `p−1` units on the diagonal) and the off-diagonal
  `−1` (`gauss_conj_offdiag`) together state `g·conj g = p·e_0 − Σ_k e_k = p·1 − N` in `R[C_p]`.  This
  is the `|g(χ)|²`-structure feeding the Jacobi-sum norm `N(J)=p` (the pure convolution identity
  `N⋆N = p·N`, then the Gauss–Jacobi relation `g(χ)²=J·g(χ²)`).  ∅-axiom. -/
theorem gauss_conj_norm {d : ZOmega} {p m x k : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ t, t ∣ p → t = 1 ∨ t = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hkp : k < p) :
    conv p (gauss p m x) (gaussConj p m x) k
      = (if k = 0 then ofInt (((p - 1 : Nat)) : Int) else ofInt (-1)) := by
  rcases Nat.eq_zero_or_pos k with hz | hpos
  · subst hz; rw [if_pos rfl]; exact gauss_conj_zero p m x
  · have hne : k ≠ 0 := fun h => absurd (h ▸ hpos) (by decide)
    rw [if_neg hne]
    exact gauss_conj_offdiag hp hp3 hpr h3m hm1 hdn hω hx hpos hkp

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne
