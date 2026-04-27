/-!
# Research.PrimeDescentObservations: descent template 의 boundary 관찰

`Sqrt2/3/5IrrationalPure` 의 robustness 의 *boundary* 의 직접
실험.

## 관 찰 1: Sqrt4 (perfect square) — descent FAILS, sqrt4 = 2 rational

`m * m = 4 * (k * k)` has concrete rational solution: m = 2, k = 1.
즉 (sqrt 4) = 2.  Descent template 이 *작동 안 함* — squaring
kernel 이 {0, 2} mod 4 (not trivial).

## 관 찰 2: Sqrt6 (squarefree composite) — descent works

Squaring map mod 6: {0² → 0, 1² → 1, 2² → 4, 3² → 3, 4² → 4,
5² → 1}.  Kernel = {0}.  Hence m² ≡ 0 mod 6 → m ≡ 0 mod 6 →
descent works.  (Full implementation: 6-case polynomial identities,
mechanical.)

## 관 찰 3: Sqrt8 (non-squarefree) — descent FAILS, sqrt8 = 2*sqrt2

`m² = 8 * k²` has solution m = 2k*sqrt2 (irrational), but
mod 8 squaring map: {0² → 0, 1² → 1, 2² → 4, 3² → 1, 4² → 0,
5² → 1, 6² → 4, 7² → 1}.  Kernel = {0, 4}.  Not trivial.

descent for sqrt8 directly fails; 대 신 sqrt8 = 2·sqrt2 →
sqrt2 의 descent.

## Conclusion

Descent template 이 *exactly* squarefree N 에 대 해 작동.
Non-squarefree N: factor out square 후 squarefree 부분 의
descent 로 환원.
-/

namespace E213.Research.PrimeDescentObservations

/-- **관 찰 1**: m = 2, k = 1 이 m² = 4k² 의 해 — sqrt4 = 2 rational. -/
theorem sqrt4_rational : ∃ m k : Nat, k ≥ 1 ∧ m * m = 4 * (k * k) :=
  ⟨2, 1, Nat.le_refl 1, rfl⟩

/-- **관 찰 1 의 직접 의미**: descent template 이 sqrt4 에 대 해
    작동 *불가능* — 그렇 다 면 contradiction (rational solution 존재). -/
theorem sqrt4_not_irrational :
    ¬ (∀ k m : Nat, k ≥ 1 → m * m ≠ 4 * (k * k)) := by
  intro h
  exact h 1 2 (Nat.le_refl 1) rfl

/-- **관 찰 3**: m = 4, k = 1 — sqrt(16) = 4. -/
theorem sqrt16_rational : ∃ m k : Nat, k ≥ 1 ∧ m * m = 16 * (k * k) :=
  ⟨4, 1, Nat.le_refl 1, rfl⟩

end E213.Research.PrimeDescentObservations
