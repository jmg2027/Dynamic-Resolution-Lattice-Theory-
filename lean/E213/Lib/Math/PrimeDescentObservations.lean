/-!
# PrimeDescentObservations: boundary observations of descent template

Direct experiment at the *boundary* of the robustness of
`Sqrt2/3/5IrrationalPure`.

## Observation 1: Sqrt4 (perfect square) — descent FAILS, sqrt4 = 2 rational

`m * m = 4 * (k * k)` has a concrete rational solution: m = 2, k = 1.
That is, sqrt(4) = 2.  The descent template *does not work* — the
squaring kernel is {0, 2} mod 4 (not trivial).

## Observation 2: Sqrt6 (squarefree composite) — descent works

Squaring map mod 6: {0² → 0, 1² → 1, 2² → 4, 3² → 3, 4² → 4,
5² → 1}.  Kernel = {0}.  Hence m² ≡ 0 mod 6 → m ≡ 0 mod 6 →
descent works.  (Full implementation: 6-case polynomial identities,
mechanical.)

## Observation 3: Sqrt8 (non-squarefree) — descent FAILS, sqrt8 = 2*sqrt2

`m² = 8 * k²` has solution m = 2k*sqrt2 (irrational), but mod 8
squaring map: {0² → 0, 1² → 1, 2² → 4, 3² → 1, 4² → 0, 5² → 1,
6² → 4, 7² → 1}.  Kernel = {0, 4}.  Not trivial.

Descent for sqrt8 fails directly; instead reduce sqrt8 = 2·sqrt2 →
descent for sqrt2.

## Conclusion

The descent template works *exactly* for squarefree N.
For non-squarefree N: factor out the square, then reduce to the descent
for the squarefree part.
-/

namespace E213.Lib.Math.PrimeDescentObservations

/-- **Observation 1**: m = 2, k = 1 solves m² = 4k² — sqrt4 = 2 rational. -/
theorem sqrt4_rational : ∃ m k : Nat, k ≥ 1 ∧ m * m = 4 * (k * k) :=
  ⟨2, 1, Nat.le_refl 1, rfl⟩

/-- **Direct implication of Observation 1**: the descent template
    *cannot* work for sqrt4 — if it did, contradiction (rational
    solution exists). -/
theorem sqrt4_not_irrational :
    ¬ (∀ k m : Nat, k ≥ 1 → m * m ≠ 4 * (k * k)) := by
  intro h
  exact h 1 2 (Nat.le_refl 1) rfl

/-- **Observation 3**: m = 4, k = 1 — sqrt(16) = 4. -/
theorem sqrt16_rational : ∃ m k : Nat, k ≥ 1 ∧ m * m = 16 * (k * k) :=
  ⟨4, 1, Nat.le_refl 1, rfl⟩

end E213.Lib.Math.PrimeDescentObservations
