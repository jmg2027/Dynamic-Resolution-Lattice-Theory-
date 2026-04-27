import E213.Research.ArchimedeanCauchy

/-!
# Research.HasModulus: Constructive Cauchy modulus typeclass

PAPER1 §6.4 의 LEM-bound `∀ (m, k), ∃ N` closure 를 우회 하는
정통 Bishop-style infrastructure: explicit modulus 를 *data*
로 요구.

## 핵심

`HasModulus xs`: sequence `xs : Nat → Raw` 에 대 한 explicit
N : Nat → Nat → Nat (per-(m, k) modulus) 의 typeclass
embedding.  data 가 주어지면 isOrderCauchy 가 LEM 없 이
derive.

## 의의

- *Sequence supplier 가 modulus 를 함께 제공* 하는 정통
  constructive analysis pattern (Bishop 1967).
- `HasModulus → isOrderCauchy` 가 trivially 성립 — typeclass
  보유 가 LEM 우회 의 mechanical replacement.
- 구체 instance (Pell, Euler, Wallis) 는 future work; 각각
  explicit N 함수 의 구성 이 부담 (Pell: y_n ≥ k iff n ≥ k 의
  bound 로 closed form 가능; Euler/Wallis: irrationality of
  e/π/2 가 framework-internal lemma 로 격상 되 어야 — 별도
  arc).
-/

namespace E213.Research.HasModulusNS

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- **Constructive Cauchy modulus**: explicit per-(m, k)
    modulus N 으로 orderProj 의 stabilization 을 data 로
    carry.  Bishop-style constructive analysis 의 정통
    pattern. -/
structure HasModulus (xs : Nat → Raw) where
  N : Nat → Nat → Nat
  cauchy_at : ∀ m k, k ≥ 1 → ∀ i j, i ≥ N m k → j ≥ N m k →
    orderProj m k (abLens.view (xs i)) = orderProj m k (abLens.view (xs j))

/-- **Modulus implies isOrderCauchy** — trivial extraction. -/
theorem isOrderCauchy_of_hasModulus (xs : Nat → Raw)
    (h : HasModulus xs) : isOrderCauchy xs := by
  intro m k hk
  exact ⟨h.N m k, h.cauchy_at m k hk⟩

end E213.Research.HasModulusNS
