import E213.Theory.Closed.Nat213Bridge
import E213.Lib.Math.Real213.CutPoset
import E213.Lib.Math.Real213.CutSumComm
import E213.Term.Tactic.Nat213

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

namespace E213.Lib.Math.Real213.ChainToCut

open E213.Theory

/-- Chain (Method A Raw) → Dedekind cut.  chain `r` 의 leaves count
    `value r` 가 정수 cut 의 분자 (분모 1). -/
def chainToCut (r : Raw) : Nat → Nat → Bool :=
  fun m k => decide (Theory.Closed.Nat213.value r * k ≤ m)

/-- Definition unfolding — convenience. -/
theorem chainToCut_def (r : Raw) (m k : Nat) :
    chainToCut r m k = decide (Theory.Closed.Nat213.value r * k ≤ m) := rfl

/-- **Numeral correspondence**: numeral n 의 chain image 가 정수 (n+1)
    의 cut.  `value (numeral n) = n + 1` substitution. -/
theorem chainToCut_numeral (n : Nat) (m k : Nat) :
    chainToCut (Theory.Closed.Nat213.numeral n) m k = decide ((n + 1) * k ≤ m) := by
  show decide (Theory.Closed.Nat213.value (Theory.Closed.Nat213.numeral n) * k ≤ m)
     = decide ((n + 1) * k ≤ m)
  rw [Theory.Closed.Nat213.value_numeral]

/-! ### Layer 2 image bridge — toRaw chain → Lean Nat cut -/

open E213.Theory.Closed.Nat213Bridge (toRaw value_toRaw value_add value_mul)

/-- **toRaw image 의 cut**: Layer 2 element m 의 chain image 가 정수
    `m.toNat` 의 cut. -/
theorem chainToCut_toRaw (m : Theory.Nat213.Nat213) (mu k : Nat) :
    chainToCut (toRaw m) mu k = decide (m.toNat * k ≤ mu) := by
  show decide (Theory.Closed.Nat213.value (toRaw m) * k ≤ mu)
     = decide (m.toNat * k ≤ mu)
  rw [value_toRaw]

/-- **Add homomorphism (pointwise)**: closed-Raw add 의 chain image 가
    Lean Nat add 의 cut.  closed-Raw 산술이 Real213 cut 산술로 lift. -/
theorem chainToCut_add (m n : Theory.Nat213.Nat213) (mu k : Nat) :
    chainToCut (Theory.Closed.Nat213.add (toRaw m) (toRaw n)) mu k
      = decide ((m.toNat + n.toNat) * k ≤ mu) := by
  show decide (Theory.Closed.Nat213.value
                  (Theory.Closed.Nat213.add (toRaw m) (toRaw n)) * k ≤ mu)
     = decide ((m.toNat + n.toNat) * k ≤ mu)
  rw [value_add, value_toRaw, value_toRaw]

/-- **Mul homomorphism (pointwise)**: closed-Raw mul 의 chain image 가
    Lean Nat mul 의 cut. -/
theorem chainToCut_mul (m n : Theory.Nat213.Nat213) (mu k : Nat) :
    chainToCut (Theory.Closed.Nat213.mul (toRaw m) (toRaw n)) mu k
      = decide ((m.toNat * n.toNat) * k ≤ mu) := by
  show decide (Theory.Closed.Nat213.value
                  (Theory.Closed.Nat213.mul (toRaw m) (toRaw n)) * k ≤ mu)
     = decide ((m.toNat * n.toNat) * k ≤ mu)
  rw [value_mul, value_toRaw, value_toRaw]

/-! ### cutSum compatibility — Real213 cutSum 와 chain bridge 의 commute

가장 substantial 결과: 두 chain 의 add 가 Real213 cutSum 과 정확히 일치.
이게 Theory/Closed/* 의 산술이 Real213 cut 우주 위에서 그대로 작동함의
정확한 증거.  G84 Tier 4 의 진정한 evidence. -/

open E213.Lib.Math.Real213.CutSum (cutSum cutSumAux)
open E213.Lib.Math.Real213.CutSumComm (cutSumAux_eq_true_iff)

/-- 보조: `x * (2*k) = 2 * x * k`.  Nat213.mul_assoc + Nat.mul_comm. -/
private theorem mul_two_mul (x k : Nat) : x * (2*k) = 2 * x * k := by
  rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm x 2]

/-- 보조: 두 Bool 이 `(· = true)` 동치이면 같음. -/
private theorem bool_eq_of_iff_true (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- **★ Iff 핵심 ★**: integer chain 의 cutSum 의 truth value 가
    `(a + b) * k ≤ m` 과 동치. -/
theorem cutSum_chainToCut_iff (a b : Theory.Nat213.Nat213) (m k : Nat) :
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
      E213.Tactic.Nat213.add_sub_of_le hi_le ▸ Nat.add_le_add h1 h2
    have h4 : 2 * ((a.toNat + b.toNat) * k) ≤ 2 * m := by
      calc 2 * ((a.toNat + b.toNat) * k)
          = 2 * (a.toNat + b.toNat) * k := (E213.Tactic.Nat213.mul_assoc _ _ _).symm
        _ = (a.toNat + b.toNat) * (2*k) := (mul_two_mul _ _).symm
        _ = a.toNat * (2*k) + b.toNat * (2*k) := E213.Tactic.Nat213.add_mul _ _ _
        _ ≤ 2 * m := h3
    exact Nat.le_of_mul_le_mul_left h4 (by decide : 0 < 2)
  · intro hsum
    refine ⟨2 * a.toNat * k, ?_, ?_, ?_⟩
    · have hAk : a.toNat * k ≤ m := by
        calc a.toNat * k ≤ a.toNat * k + b.toNat * k := Nat.le_add_right _ _
          _ = (a.toNat + b.toNat) * k := (E213.Tactic.Nat213.add_mul _ _ _).symm
          _ ≤ m := hsum
      calc 2 * a.toNat * k = 2 * (a.toNat * k) := E213.Tactic.Nat213.mul_assoc _ _ _
        _ ≤ 2 * m := Nat.mul_le_mul_left 2 hAk
    · have heq : a.toNat * (2*k) = 2 * a.toNat * k := mul_two_mul _ _
      have : decide (a.toNat * (2*k) ≤ 2 * a.toNat * k) = true :=
        decide_eq_true (heq ▸ Nat.le_refl _)
      exact (chainToCut_toRaw a (2 * a.toNat * k) (2*k)).symm ▸ this
    · have h2sum : 2 * a.toNat * k + 2 * b.toNat * k ≤ 2*m := by
        calc 2 * a.toNat * k + 2 * b.toNat * k
            = a.toNat * (2*k) + b.toNat * (2*k) := by
              rw [mul_two_mul, mul_two_mul]
          _ = (a.toNat + b.toNat) * (2*k) := (E213.Tactic.Nat213.add_mul _ _ _).symm
          _ = 2 * (a.toNat + b.toNat) * k := mul_two_mul _ _
          _ = 2 * ((a.toNat + b.toNat) * k) := E213.Tactic.Nat213.mul_assoc _ _ _
          _ ≤ 2 * m := Nat.mul_le_mul_left 2 hsum
      have hBk : 2 * b.toNat * k ≤ 2*m - 2 * a.toNat * k :=
        E213.Tactic.Nat213.le_sub_of_add_le ((Nat.add_comm _ _) ▸ h2sum)
      have heq : b.toNat * (2*k) = 2 * b.toNat * k := mul_two_mul _ _
      have : decide (b.toNat * (2*k) ≤ 2*m - 2 * a.toNat * k) = true :=
        decide_eq_true (heq ▸ hBk)
      exact (chainToCut_toRaw b (2*m - 2 * a.toNat * k) (2*k)).symm ▸ this

/-- **★ cutSum compatibility ★**: Real213 cutSum 이 closed-Raw add 의
    bridge 와 commute.  G84 Tier 4 의 정확한 증거 — closed-Raw 산술이
    Real213 cut 우주에서 그대로 작동. -/
theorem cutSum_chainToCut (a b : Theory.Nat213.Nat213) (m k : Nat) :
    cutSum (chainToCut (toRaw a)) (chainToCut (toRaw b)) m k
      = chainToCut (Theory.Closed.Nat213.add (toRaw a) (toRaw b)) m k := by
  rw [chainToCut_add]
  apply bool_eq_of_iff_true
  constructor
  · intro h
    exact decide_eq_true ((cutSum_chainToCut_iff a b m k).mp h)
  · intro h
    exact (cutSum_chainToCut_iff a b m k).mpr (of_decide_eq_true h)

end E213.Lib.Math.Real213.ChainToCut
