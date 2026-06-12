import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev

/-!
# FactorialLcmDvd — `k ∣ n!` and `lcm(1..n) ∣ n!`, ∅-axiom

The factorial-clearing inputs for the ζ(3) reduced presentation (the
recurrence-divisibility route to `zeta3HolonomicReal`): every `k ≤ n` divides
`n!`, hence `lcm(1..n) ∣ n!` (the universal property of `lcmUpTo`).  The common
factor `c n = (n!)³/(2·lcm³)` of the Apéry convergents is built on these.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FactorialLcmDvd

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (lcmUpTo lcmUpTo_dvd)

/-- Every positive `k ≤ n` divides `n!` (subtraction-free; `Nat.dvd_trans` carries
    propext, so the `k ≤ n` step composes the two dvd witnesses by hand). -/
theorem dvd_factorial {k : Nat} (hk : 0 < k) : ∀ {n : Nat}, k ≤ n → k ∣ factorial n := by
  intro n
  induction n with
  | zero => intro hkn; exact absurd (Nat.lt_of_lt_of_le hk hkn) (Nat.lt_irrefl 0)
  | succ n ih =>
    intro hkn
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · rcases ih (Nat.le_of_lt_succ hlt) with ⟨c, hc⟩
      exact ⟨(n + 1) * c, by rw [factorial_succ, hc]; ring_nat⟩
    · have heq : k = n + 1 := Nat.le_antisymm hkn hge
      exact ⟨factorial n, by rw [heq, factorial_succ]⟩

/-- `lcm(1..n) ∣ n!` — `n!` is a common multiple of `1..n`, so the least common
    multiple divides it (`lcmUpTo`'s universal property). -/
theorem lcmUpTo_dvd_factorial (n : Nat) : lcmUpTo n ∣ factorial n :=
  lcmUpTo_dvd (fun _ hk hkn => dvd_factorial hk hkn)

end E213.Lib.Math.NumberTheory.FactorialLcmDvd
