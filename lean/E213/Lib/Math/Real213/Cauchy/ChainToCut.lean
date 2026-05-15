import E213.Lens.Number
import E213.Lib.Math.Real213.Core.CutPoset
import E213.Lib.Math.Real213.Sum.CutSumComm
import E213.Lib.Math.Real213.Mul.CutMulComm
import E213.Meta.Tactic.NatHelper

/-!
# Real213.ChainToCut — Closed Nat213 chain → Real213 cut bridge

Method A Raw chain (`Theory.Closed.Nat213`) 가 Real213 의 cut 우주에
자연스럽게 embed.  chain `r` 의 leaves count `n = value r` 가 정수
n 의 Dedekind cut 에 대응.

이게 G84 Tier 4 의 핵심 bridge — Theory/Closed/* 가 self-contained
island 가 아니라 Real213 의 실제 압축 도구임을 입증.

## 대응

  - `value (numeral n) = n + 1` (Method A 의 leaves count)
  - chain → cut: `chainToCut r = constCut (value r) 1`
                  = `fun m k => decide (value r * k ≤ m)`
  - 정수 v 의 Dedekind cut: "v ≤ m/k" iff "v*k ≤ m"
-/

namespace E213.Lib.Math.Real213.Cauchy.ChainToCut

open E213.Theory

/-- Chain (Method A Raw) → Dedekind cut.  chain `r` 의 leaves count
    `value r` 가 정수 cut 의 분자 (분모 1). -/
def chainToCut (r : Raw) : Nat → Nat → Bool :=
  fun m k => decide (E213.Lens.Number.Nat213.Raw.value r * k ≤ m)

/-- Definition unfolding — convenience. -/
theorem chainToCut_def (r : Raw) (m k : Nat) :
    chainToCut r m k = decide (E213.Lens.Number.Nat213.Raw.value r * k ≤ m) := rfl

/-- **Numeral correspondence**: numeral n 의 chain image 가 정수 (n+1)
    의 cut.  `value (numeral n) = n + 1` substitution. -/
theorem chainToCut_numeral (n : Nat) (m k : Nat) :
    chainToCut (E213.Lens.Number.Nat213.Raw.numeral n) m k = decide ((n + 1) * k ≤ m) := by
  show decide (E213.Lens.Number.Nat213.Raw.value (E213.Lens.Number.Nat213.Raw.numeral n) * k ≤ m)
     = decide ((n + 1) * k ≤ m)
  rw [E213.Lens.Number.Nat213.Raw.value_numeral]

/-! ### Layer 2 image bridge — toRaw chain → Lean Nat cut -/

open E213.Lens.Number.Nat213.Bridge (toRaw value_toRaw value_add value_mul)

/-- **toRaw image 의 cut**: Layer 2 element m 의 chain image 가 정수
    `m.toNat` 의 cut. -/
theorem chainToCut_toRaw (m : E213.Lens.Number.Nat213.Peano.Nat213) (mu k : Nat) :
    chainToCut (toRaw m) mu k = decide (m.toNat * k ≤ mu) := by
  show decide (E213.Lens.Number.Nat213.Raw.value (toRaw m) * k ≤ mu)
     = decide (m.toNat * k ≤ mu)
  rw [value_toRaw]

/-- **Add homomorphism (pointwise)**: closed-Raw add 의 chain image 가
    Lean Nat add 의 cut.  closed-Raw 산술이 Real213 cut 산술로 lift. -/
theorem chainToCut_add (m n : E213.Lens.Number.Nat213.Peano.Nat213) (mu k : Nat) :
    chainToCut (E213.Lens.Number.Nat213.Raw.add (toRaw m) (toRaw n)) mu k
      = decide ((m.toNat + n.toNat) * k ≤ mu) := by
  show decide (E213.Lens.Number.Nat213.Raw.value
                  (E213.Lens.Number.Nat213.Raw.add (toRaw m) (toRaw n)) * k ≤ mu)
     = decide ((m.toNat + n.toNat) * k ≤ mu)
  rw [value_add, value_toRaw, value_toRaw]

/-- **Mul homomorphism (pointwise)**: closed-Raw mul 의 chain image 가
    Lean Nat mul 의 cut. -/
theorem chainToCut_mul (m n : E213.Lens.Number.Nat213.Peano.Nat213) (mu k : Nat) :
    chainToCut (E213.Lens.Number.Nat213.Raw.mul (toRaw m) (toRaw n)) mu k
      = decide ((m.toNat * n.toNat) * k ≤ mu) := by
  show decide (E213.Lens.Number.Nat213.Raw.value
                  (E213.Lens.Number.Nat213.Raw.mul (toRaw m) (toRaw n)) * k ≤ mu)
     = decide ((m.toNat * n.toNat) * k ≤ mu)
  rw [value_mul, value_toRaw, value_toRaw]

/-! ### cutSum compatibility — Real213 cutSum 와 chain bridge 의 commute

가장 substantial 결과: 두 chain 의 add 가 Real213 cutSum 과 정확히 일치.
이게 Theory/Closed/* 의 산술이 Real213 cut 우주 위에서 그대로 작동함의
정확한 증거.  G84 Tier 4 의 진정한 evidence. -/

open E213.Lib.Math.Real213.Sum.CutSum (cutSum cutSumAux)
open E213.Lib.Math.Real213.Sum.CutSumComm (cutSumAux_eq_true_iff)

/-- 보조: `x * (2*k) = 2 * x * k`.  Nat213.mul_assoc + Nat.mul_comm. -/
private theorem mul_two_mul (x k : Nat) : x * (2*k) = 2 * x * k := by
  rw [← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm x 2]

/-- 보조: 두 Bool 이 `(· = true)` 동치이면 같음. -/
private theorem bool_eq_of_iff_true (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **★ Iff 핵심 ★**: integer chain 의 cutSum 의 truth value 가
    `(a + b) * k ≤ m` 과 동치. -/
theorem cutSum_chainToCut_iff (a b : E213.Lens.Number.Nat213.Peano.Nat213) (m k : Nat) :
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

/-- **★ cutSum compatibility ★**: Real213 cutSum 이 closed-Raw add 의
    bridge 와 commute.  G84 Tier 4 의 정확한 증거 — closed-Raw 산술이
    Real213 cut 우주에서 그대로 작동. -/
theorem cutSum_chainToCut (a b : E213.Lens.Number.Nat213.Peano.Nat213) (m k : Nat) :
    cutSum (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k
      = chainToCut (E213.Lens.Number.Nat213.Raw.add (toRaw a) (toRaw b)) m k := by
  rw [chainToCut_add]
  apply bool_eq_of_iff_true
  constructor
  · intro h
    exact decide_eq_true ((cutSum_chainToCut_iff a b m k).mp h)
  · intro h
    exact (cutSum_chainToCut_iff a b m k).mpr (of_decide_eq_true h)

end E213.Lib.Math.Real213.Cauchy.ChainToCut

namespace E213.Lib.Math.Real213.Cauchy.ChainToCut

open E213.Theory
open E213.Lens.Number.Nat213.Bridge (toRaw value_toRaw value_mul)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutMulComm (cutMulOuter_eq_true_iff)

/-! ### cutMul compatibility — Real213 cutMul 와 chain bridge 의 commute

cutSum 과 같은 패턴 mul 쪽.  closed-Raw mul 이 Real213 cutMul 과 정확히
일치 (point 별).  Nat213 의 toNat ≥ 1 invariant 가 bound check 의 enabler. -/

/-- 보조: `(a*k)*(b*k) = (a*b*k)*k`.  mul_mul_mul_comm + mul_assoc. -/
private theorem prod_rearrange (a b k : Nat) :
    a * k * (b * k) = a * b * k * k := by
  rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213,
      ← E213.Tactic.NatHelper.mul_assoc]

/-- 보조: `m ≤ (m+1)*(k+1)`.  trivial bound. -/
private theorem le_succ_mul_succ (m k : Nat) : m ≤ (m+1)*(k+1) := by
  calc m ≤ m + 1 := Nat.le_succ m
    _ = (m+1) * 1 := (Nat.mul_one (m+1)).symm
    _ ≤ (m+1) * (k+1) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))

/-- **★ Iff 핵심 (mul) ★**: integer chain 의 cutMul 의 truth value 가
    `a*b*k ≤ m` 과 동치.  Nat213.toNat_ge_one 가 enabler. -/
theorem cutMul_chainToCut_iff (a b : E213.Lens.Number.Nat213.Peano.Nat213) (m k : Nat) :
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

/-- **★ cutMul compatibility ★**: Real213 cutMul 이 closed-Raw mul 의
    bridge 와 commute.  cutSum 과 함께 + family 산술 전체 lift. -/
theorem cutMul_chainToCut (a b : E213.Lens.Number.Nat213.Peano.Nat213) (m k : Nat) :
    cutMul (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k
      = chainToCut (E213.Lens.Number.Nat213.Raw.mul (toRaw a) (toRaw b)) m k := by
  rw [chainToCut_mul]
  apply bool_eq_of_iff_true
  constructor
  · intro h
    exact decide_eq_true ((cutMul_chainToCut_iff a b m k).mp h)
  · intro h
    exact (cutMul_chainToCut_iff a b m k).mpr (of_decide_eq_true h)

/-! ### cutLe compatibility — order 보존 (chain → cut)

bounded search 없는 단순 case.  closed-Raw 의 ≤ (Nat213.toNat 통해) 가
Real213 cutLe 와 정확히 commute. -/

open E213.Lib.Math.Real213.Core.CutPoset (cutLe)

/-- **Order 보존**: chain a ≤ chain b iff a ≤ b (as Nat213.toNat). -/
theorem cutLe_chainToCut_iff (a b : E213.Lens.Number.Nat213.Peano.Nat213) :
    cutLe (chainToCut (toRaw a)) (chainToCut (toRaw b)) ↔ a.toNat ≤ b.toNat := by
  constructor
  · intro h
    -- Take (m, k) = (b.toNat, 1).  chain b at this point is true.
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

end E213.Lib.Math.Real213.Cauchy.ChainToCut

namespace E213.Lib.Math.Real213.Cauchy.ChainToCut

open E213.Theory
open E213.Lens.Number.Nat213.Bridge (toRaw)
open E213.Lib.Math.Real213.Lattice.CutMaxMin (cutMax cutMin)
open E213.Lib.Math.Real213.Core.CutPoset
  (cutLe cutLe_trans cutLe_cutMax_left cutLe_cutMax_right cutMax_lub
   cutLe_cutMin_left cutLe_cutMin_right cutMin_glb)

/-! ### Lattice characterization — cutMax / cutMin 위 chain bridge

Nat213.toNat 의 max/min 정의 없이도, cutLe + lattice 정리들로 cutMax /
cutMin 의 chain bridge characterization 달성.

`cutMax (chain a) (chain b)` 가 chain a, chain b 의 LUB → cutLe 통해
"양쪽 ≤ chain c iff a ≤ c ∧ b ≤ c".

대칭으로 cutMin 은 GLB. -/

/-- **cutMax LUB characterization**: cutMax (chain a) (chain b) ≤ chain c
    iff a ≤ c ∧ b ≤ c (둘 다 ≤ c). -/
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

/-- **cutMin GLB characterization**: chain c ≤ cutMin (chain a) (chain b)
    iff c ≤ a ∧ c ≤ b (c ≤ both). -/
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

end E213.Lib.Math.Real213.Cauchy.ChainToCut
