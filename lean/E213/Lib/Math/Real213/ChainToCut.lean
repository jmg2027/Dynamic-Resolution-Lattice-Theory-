import E213.Theory.Closed.Nat213Bridge
import E213.Lib.Math.Real213.CutPoset

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

open E213.Theory.Closed.Nat213Bridge (toRaw value_toRaw value_add)

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

end E213.Lib.Math.Real213.ChainToCut
