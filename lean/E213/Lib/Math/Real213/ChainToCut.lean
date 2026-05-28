import E213.Lens.Number
import E213.Lib.Math.Real213.Core.CutPoset
import E213.Lib.Math.Real213.Sum.CutSumComm
import E213.Lib.Math.Real213.Mul.CutMulComm
import E213.Meta.Tactic.BoolHelper
import E213.Meta.Tactic.NatHelper

/-!
# Real213.ChainToCut — Method A chain → Real213 cut bridge

The Method A Raw chain embeds naturally into the Real213 cut
universe.  For chain `r`, its leaves count `n = value r` corresponds
to the Dedekind cut of the integer `n`.

This is the G84 Tier 4 bridge — evidence that the chart objects
are usable inside Real213's actual machinery.

## Correspondence

  - `value (numeral n) = n + 1` (Method A's off-by-one)
  - chain → cut: `chainToCut r m k = decide (value r * k ≤ m)`
  - integer v's Dedekind cut: "v ≤ m/k" iff "v*k ≤ m"

## Arithmetic homomorphism level

Arithmetic homomorphism is expressed at the Peano level via
`Lens.Number.Nat213.Bridge.value_toRaw_add` /
`value_toRaw_mul`, which extract the sequence values.
-/

namespace E213.Lib.Math.Real213.ChainToCut

open E213.Theory

/-- Chain (Method A Raw) → Dedekind cut. -/
def chainToCut (r : Raw) : Nat → Nat → Bool :=
  fun m k => decide (E213.Lens.Number.Nat213.Raw.value r * k ≤ m)

theorem chainToCut_def (r : Raw) (m k : Nat) :
    chainToCut r m k
      = decide (E213.Lens.Number.Nat213.Raw.value r * k ≤ m) := rfl

/-- **Numeral correspondence**: `numeral n`'s chain image is the cut
    of the integer `n+1`. -/
theorem chainToCut_numeral (n m k : Nat) :
    chainToCut (E213.Lens.Number.Nat213.Raw.numeral n) m k
      = decide ((n + 1) * k ≤ m) := by
  show decide (E213.Lens.Number.Nat213.Raw.value
                  (E213.Lens.Number.Nat213.Raw.numeral n) * k ≤ m)
     = decide ((n + 1) * k ≤ m)
  rw [E213.Lens.Number.Nat213.Raw.value_numeral]

/-! ### Peano.Nat213 image bridge — toRaw chain → Nat cut -/

open E213.Lens.Number.Nat213.Bridge (toRaw value_toRaw value_toRaw_add value_toRaw_mul)

/-- **`toRaw` image's cut**: the Peano.Nat213 element `m`'s
    chain image agrees with the cut of the integer `m.toNat`. -/
theorem chainToCut_toRaw (m : E213.Lens.Number.Nat213.Peano.Nat213) (mu k : Nat) :
    chainToCut (toRaw m) mu k = decide (m.toNat * k ≤ mu) := by
  show decide (E213.Lens.Number.Nat213.Raw.value (toRaw m) * k ≤ mu)
     = decide (m.toNat * k ≤ mu)
  rw [value_toRaw]

/-- **Add homomorphism (pointwise)**: the cut of `toRaw (m + n)`
    matches the additive cut.  Uses Peano arithmetic since
    Raw-level arithmetic no longer exists. -/
theorem chainToCut_addPeano (m n : E213.Lens.Number.Nat213.Peano.Nat213)
    (mu k : Nat) :
    chainToCut (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.add m n)) mu k
      = decide ((m.toNat + n.toNat) * k ≤ mu) := by
  show decide (E213.Lens.Number.Nat213.Raw.value
                  (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.add m n)) * k ≤ mu)
     = decide ((m.toNat + n.toNat) * k ≤ mu)
  rw [value_toRaw_add]

/-- **Mul homomorphism (pointwise)**: the cut of `toRaw (m · n)`
    matches the multiplicative cut. -/
theorem chainToCut_mulPeano (m n : E213.Lens.Number.Nat213.Peano.Nat213)
    (mu k : Nat) :
    chainToCut (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.mul m n)) mu k
      = decide ((m.toNat * n.toNat) * k ≤ mu) := by
  show decide (E213.Lens.Number.Nat213.Raw.value
                  (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.mul m n)) * k ≤ mu)
     = decide ((m.toNat * n.toNat) * k ≤ mu)
  rw [value_toRaw_mul]

/-! ### cutSum compatibility — Real213 cutSum commutes with the chain bridge -/

open E213.Lib.Math.Real213.Sum.CutSum (cutSum cutSumAux)
open E213.Lib.Math.Real213.Sum.CutSumComm (cutSumAux_eq_true_iff)

/-- Helper: `x * (2*k) = 2 * x * k`. -/
private theorem mul_two_mul (x k : Nat) : x * (2*k) = 2 * x * k := by
  rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm x 2]

open E213.Tactic.BoolHelper (bool_eq_iff)

/-- **★ cutSum iff ★**: the cutSum on two chain images is true iff
    `(a + b) * k ≤ m`. -/
theorem cutSum_chainToCut_iff (a b : E213.Lens.Number.Nat213.Peano.Nat213)
    (m k : Nat) :
    cutSum (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k = true
    ↔ (a.toNat + b.toNat) * k ≤ m := by
  show cutSumAux _ _ k (2*m) (2*m) = true ↔ _
  refine Iff.trans (cutSumAux_eq_true_iff _ _ _ _ _) ?_
  constructor
  · rintro ⟨i, hi_le, hcxi, hcyi⟩
    have h1 : a.toNat * (2*k) ≤ i :=
      of_decide_eq_true (chainToCut_toRaw a i (2*k) ▸ hcxi)
    have h2 : b.toNat * (2*k) ≤ 2*m - i :=
      of_decide_eq_true (chainToCut_toRaw b (2*m - i) (2*k) ▸ hcyi)
    have h3 : a.toNat * (2*k) + b.toNat * (2*k) ≤ 2*m :=
      E213.Tactic.NatHelper.add_sub_of_le hi_le ▸ Nat.add_le_add h1 h2
    have h4 : 2 * ((a.toNat + b.toNat) * k) ≤ 2 * m := by
      calc 2 * ((a.toNat + b.toNat) * k)
          = 2 * (a.toNat + b.toNat) * k := (E213.Tactic.NatHelper.mul_assoc _ _ _).symm
        _ = (a.toNat + b.toNat) * (2*k) := (mul_two_mul _ _).symm
        _ = a.toNat * (2*k) + b.toNat * (2*k) := E213.Tactic.NatHelper.add_mul _ _ _
        _ ≤ 2 * m := h3
    exact Nat.le_of_mul_le_mul_left h4 (by decide : 0 < 2)
  · intro hsum
    refine ⟨2 * a.toNat * k, ?_, ?_, ?_⟩
    · have hAk : a.toNat * k ≤ m := by
        calc a.toNat * k ≤ a.toNat * k + b.toNat * k := Nat.le_add_right _ _
          _ = (a.toNat + b.toNat) * k := (E213.Tactic.NatHelper.add_mul _ _ _).symm
          _ ≤ m := hsum
      calc 2 * a.toNat * k = 2 * (a.toNat * k) := E213.Tactic.NatHelper.mul_assoc _ _ _
        _ ≤ 2 * m := Nat.mul_le_mul_left 2 hAk
    · have heq : a.toNat * (2*k) = 2 * a.toNat * k := mul_two_mul _ _
      have : decide (a.toNat * (2*k) ≤ 2 * a.toNat * k) = true :=
        decide_eq_true (heq ▸ Nat.le_refl _)
      exact (chainToCut_toRaw a (2 * a.toNat * k) (2*k)).symm ▸ this
    · have h2sum : 2 * a.toNat * k + 2 * b.toNat * k ≤ 2*m := by
        calc 2 * a.toNat * k + 2 * b.toNat * k
            = a.toNat * (2*k) + b.toNat * (2*k) := by
              rw [mul_two_mul, mul_two_mul]
          _ = (a.toNat + b.toNat) * (2*k) := (E213.Tactic.NatHelper.add_mul _ _ _).symm
          _ = 2 * (a.toNat + b.toNat) * k := mul_two_mul _ _
          _ = 2 * ((a.toNat + b.toNat) * k) := E213.Tactic.NatHelper.mul_assoc _ _ _
          _ ≤ 2 * m := Nat.mul_le_mul_left 2 hsum
      have hBk : 2 * b.toNat * k ≤ 2*m - 2 * a.toNat * k :=
        E213.Tactic.NatHelper.le_sub_of_add_le ((Nat.add_comm _ _) ▸ h2sum)
      have heq : b.toNat * (2*k) = 2 * b.toNat * k := mul_two_mul _ _
      have : decide (b.toNat * (2*k) ≤ 2*m - 2 * a.toNat * k) = true :=
        decide_eq_true (heq ▸ hBk)
      exact (chainToCut_toRaw b (2*m - 2 * a.toNat * k) (2*k)).symm ▸ this

/-- **★ cutSum compatibility ★**: Real213's cutSum commutes with the
    chain bridge under Peano addition.  Replaces the previous
    Raw-level statement. -/
theorem cutSum_chainToCut (a b : E213.Lens.Number.Nat213.Peano.Nat213)
    (m k : Nat) :
    cutSum (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k
      = chainToCut (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.add a b)) m k := by
  rw [chainToCut_addPeano]
  apply bool_eq_iff
  constructor
  · intro h
    exact decide_eq_true ((cutSum_chainToCut_iff a b m k).mp h)
  · intro h
    exact (cutSum_chainToCut_iff a b m k).mpr (of_decide_eq_true h)


open E213.Lens.Number.Nat213.Bridge (toRaw value_toRaw value_toRaw_mul)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutMulComm (cutMulOuter_eq_true_iff)

/-! ### cutMul compatibility -/

private theorem prod_rearrange (a b k : Nat) :
    a * k * (b * k) = a * b * k * k := by
  rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213,
      ← E213.Tactic.NatHelper.mul_assoc]

private theorem le_succ_mul_succ (m k : Nat) : m ≤ (m+1)*(k+1) := by
  calc m ≤ m + 1 := Nat.le_succ m
    _ = (m+1) * 1 := (Nat.mul_one (m+1)).symm
    _ ≤ (m+1) * (k+1) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))

/-- **★ cutMul iff ★**: the cutMul on two chain images is true iff
    `a*b*k ≤ m`. -/
theorem cutMul_chainToCut_iff (a b : E213.Lens.Number.Nat213.Peano.Nat213)
    (m k : Nat) :
    cutMul (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k = true
    ↔ a.toNat * b.toNat * k ≤ m := by
  show cutMulOuter _ _ k m ((m+1)*(k+1)) ((m+1)*(k+1)) = true ↔ _
  refine Iff.trans (cutMulOuter_eq_true_iff _ _ _ _ _ _) ?_
  constructor
  · rintro ⟨m1, _, m2, _, hcx, hcy, hmul⟩
    have h1 : a.toNat * k ≤ m1 :=
      of_decide_eq_true (chainToCut_toRaw a m1 k ▸ hcx)
    have h2 : b.toNat * k ≤ m2 :=
      of_decide_eq_true (chainToCut_toRaw b m2 k ▸ hcy)
    have hprod : a.toNat * k * (b.toNat * k) ≤ m * k :=
      Nat.le_trans (Nat.le_trans
        (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_left m1 h2)) hmul
    rw [prod_rearrange a.toNat b.toNat k] at hprod
    cases k with
    | zero => show a.toNat * b.toNat * 0 ≤ m
              rw [Nat.mul_zero]; exact Nat.zero_le _
    | succ k' =>
      exact E213.Tactic.NatHelper.le_of_mul_le_mul_right (Nat.succ_pos k') hprod
  · intro hsum
    have ha_pos : 1 ≤ a.toNat := E213.Lens.Number.Nat213.Peano.Nat213.toNat_ge_one a
    have hb_pos : 1 ≤ b.toNat := E213.Lens.Number.Nat213.Peano.Nat213.toNat_ge_one b
    have h_ak_le_m : a.toNat * k ≤ m := by
      calc a.toNat * k = a.toNat * (1 * k) := by rw [Nat.one_mul]
        _ ≤ a.toNat * (b.toNat * k) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right k hb_pos)
        _ = a.toNat * b.toNat * k := (E213.Tactic.NatHelper.mul_assoc _ _ _).symm
        _ ≤ m := hsum
    have h_bk_le_m : b.toNat * k ≤ m := by
      calc b.toNat * k = 1 * (b.toNat * k) := (Nat.one_mul _).symm
        _ ≤ a.toNat * (b.toNat * k) := Nat.mul_le_mul_right _ ha_pos
        _ = a.toNat * b.toNat * k := (E213.Tactic.NatHelper.mul_assoc _ _ _).symm
        _ ≤ m := hsum
    refine ⟨a.toNat * k, ?_, b.toNat * k, ?_, ?_, ?_, ?_⟩
    · exact Nat.le_trans h_ak_le_m (le_succ_mul_succ m k)
    · exact Nat.le_trans h_bk_le_m (le_succ_mul_succ m k)
    · exact (chainToCut_toRaw a (a.toNat * k) k).symm ▸
        decide_eq_true (Nat.le_refl _)
    · exact (chainToCut_toRaw b (b.toNat * k) k).symm ▸
        decide_eq_true (Nat.le_refl _)
    · rw [prod_rearrange a.toNat b.toNat k]
      exact Nat.mul_le_mul_right k hsum

/-- **★ cutMul compatibility ★**: Real213's cutMul commutes with the
    chain bridge under Peano multiplication. -/
theorem cutMul_chainToCut (a b : E213.Lens.Number.Nat213.Peano.Nat213)
    (m k : Nat) :
    cutMul (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k
      = chainToCut (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.mul a b)) m k := by
  rw [chainToCut_mulPeano]
  apply bool_eq_iff
  constructor
  · intro h
    exact decide_eq_true ((cutMul_chainToCut_iff a b m k).mp h)
  · intro h
    exact (cutMul_chainToCut_iff a b m k).mpr (of_decide_eq_true h)

open E213.Lib.Math.Real213.Core.CutPoset (cutLe)

/-- **Order preservation**: chain a ≤ chain b iff a.toNat ≤ b.toNat. -/
theorem cutLe_chainToCut_iff (a b : E213.Lens.Number.Nat213.Peano.Nat213) :
    cutLe (chainToCut (toRaw a)) (chainToCut (toRaw b)) ↔ a.toNat ≤ b.toNat := by
  constructor
  · intro h
    have hbb_le : b.toNat * 1 ≤ b.toNat := by
      calc b.toNat * 1 = b.toNat := Nat.mul_one _
        _ ≤ b.toNat := Nat.le_refl _
    have hbb : chainToCut (toRaw b) b.toNat 1 = true :=
      (chainToCut_toRaw b b.toNat 1).symm ▸ decide_eq_true hbb_le
    have hab : chainToCut (toRaw a) b.toNat 1 = true := h _ _ hbb
    have hab2 : decide (a.toNat * 1 ≤ b.toNat) = true :=
      chainToCut_toRaw a b.toNat 1 ▸ hab
    have h3 : a.toNat * 1 ≤ b.toNat := of_decide_eq_true hab2
    calc a.toNat = a.toNat * 1 := (Nat.mul_one _).symm
      _ ≤ b.toNat := h3
  · intro hab m k hcb
    have hcb2 : decide (b.toNat * k ≤ m) = true :=
      chainToCut_toRaw b m k ▸ hcb
    have hbk : b.toNat * k ≤ m := of_decide_eq_true hcb2
    have hak : a.toNat * k ≤ b.toNat * k := Nat.mul_le_mul_right _ hab
    have h_ak_le_m : a.toNat * k ≤ m := Nat.le_trans hak hbk
    exact (chainToCut_toRaw a m k).symm ▸ decide_eq_true h_ak_le_m


open E213.Lens.Number.Nat213.Bridge (toRaw)
open E213.Lib.Math.Real213.Lattice.CutMaxMin (cutMax cutMin)
open E213.Lib.Math.Real213.Core.CutPoset
  (cutLe cutLe_trans cutLe_cutMax_left cutLe_cutMax_right cutMax_lub
   cutLe_cutMin_left cutLe_cutMin_right cutMin_glb)

/-! ### Lattice characterization (cutMax / cutMin on chain bridge) -/

theorem cutLe_cutMax_chainToCut_iff (a b c : E213.Lens.Number.Nat213.Peano.Nat213) :
    cutLe (cutMax (chainToCut (toRaw a)) (chainToCut (toRaw b)))
          (chainToCut (toRaw c))
    ↔ a.toNat ≤ c.toNat ∧ b.toNat ≤ c.toNat := by
  constructor
  · intro h
    have ha : cutLe (chainToCut (toRaw a)) (chainToCut (toRaw c)) :=
      cutLe_trans _ _ _ (cutLe_cutMax_left _ _) h
    have hb : cutLe (chainToCut (toRaw b)) (chainToCut (toRaw c)) :=
      cutLe_trans _ _ _ (cutLe_cutMax_right _ _) h
    exact ⟨(cutLe_chainToCut_iff a c).mp ha,
           (cutLe_chainToCut_iff b c).mp hb⟩
  · rintro ⟨ha, hb⟩
    exact cutMax_lub _ _ _
      ((cutLe_chainToCut_iff a c).mpr ha)
      ((cutLe_chainToCut_iff b c).mpr hb)

theorem cutLe_cutMin_chainToCut_iff (a b c : E213.Lens.Number.Nat213.Peano.Nat213) :
    cutLe (chainToCut (toRaw c))
          (cutMin (chainToCut (toRaw a)) (chainToCut (toRaw b)))
    ↔ c.toNat ≤ a.toNat ∧ c.toNat ≤ b.toNat := by
  constructor
  · intro h
    have ha : cutLe (chainToCut (toRaw c)) (chainToCut (toRaw a)) :=
      cutLe_trans _ _ _ h (cutLe_cutMin_left _ _)
    have hb : cutLe (chainToCut (toRaw c)) (chainToCut (toRaw b)) :=
      cutLe_trans _ _ _ h (cutLe_cutMin_right _ _)
    exact ⟨(cutLe_chainToCut_iff c a).mp ha,
           (cutLe_chainToCut_iff c b).mp hb⟩
  · rintro ⟨ha, hb⟩
    exact cutMin_glb _ _ _
      ((cutLe_chainToCut_iff c a).mpr ha)
      ((cutLe_chainToCut_iff c b).mpr hb)

end E213.Lib.Math.Real213.ChainToCut
