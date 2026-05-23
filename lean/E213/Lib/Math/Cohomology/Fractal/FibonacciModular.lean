import E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff
import E213.Meta.Nat.AddMod213

/-!
# Fibonacci-sequence modular fingerprint

Companion to `FibonacciCutoff.lean` — classical Pisano-period
result for the Fibonacci sequence mod 2.

The 2-step Fibonacci recurrence `F_{n+2} = F_{n+1} + F_n` mod 2
has period 3 (the classical Pisano period π(2) = 3).  This is
the simplest case in the Pisano-analogue family — sister to the
3-step Padovan (π_P(2) = 7) and Tribonacci (π_T(2) = 4) closures.

## Periods at small primes

| p | π(p) | first cycle (`F_0..F_{π−1} mod p`) |
|---|------|------------------------------------|
| 2 | 3    | `0, 1, 1` ★ parametric             |
| 3 | 8    | spot-checked                       |
| 5 | 20   | spot-checked                       |

## Why period 3 mod 2 is structural

The Fibonacci recurrence mod 2 is determined by the initial pair
`(F_0, F_1) = (0, 1)` mod 2.  Among `2² = 4` mod-2 pairs, the
orbit starting at `(0, 1)` visits 3 distinct pairs (the absorbing
`(0, 0)` pair is unreachable from a non-zero start) and returns:

  · `(0, 1) → (1, 1) → (1, 0) → (0, 1)`

Hence π(2) = 3.  This is the cleanest 2-step Pisano analogue;
sister to Lucas mod 2 (same orbit, same period).
-/

namespace E213.Lib.Math.Cohomology.Fractal.FibonacciModular

open E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff (Fib)
open E213.Meta.Nat.AddMod213

/-! ## §1 Mod-2 small table (decide-checked) -/

theorem Fib_0_mod_2  : Fib 0  % 2 = 0 := by decide
theorem Fib_1_mod_2  : Fib 1  % 2 = 1 := by decide
theorem Fib_2_mod_2  : Fib 2  % 2 = 1 := by decide
theorem Fib_3_mod_2  : Fib 3  % 2 = 0 := by decide
theorem Fib_4_mod_2  : Fib 4  % 2 = 1 := by decide
theorem Fib_5_mod_2  : Fib 5  % 2 = 1 := by decide
theorem Fib_6_mod_2  : Fib 6  % 2 = 0 := by decide

/-! ## §2 Period 3 mod 2 — parametric

2-step strong induction on `n`.  Base cases at `n ∈ {0, 1}`
verified by `decide`; inductive step at `n + 2` uses the
recurrence `Fib ((n+2) + 3) = Fib (n+5) = Fib (n+4) + Fib (n+3)`
combined with the matching
`Fib (n+2) = Fib (n+1) + Fib n`. -/

/-- ★ **Classical Pisano period 3 mod 2 for Fibonacci**:
    `Fib (n + 3) % 2 = Fib n % 2` for every `n : Nat`.

    Orbit on the `2² = 4` mod-2 pairs starting at `(F_0, F_1) =
    (0, 1)` cycles through 3 distinct pairs and returns — the
    absorbing `(0, 0)` pair is unreachable.  Hence π(2) = 3. -/
theorem Fib_mod_2_period_3 : ∀ n, Fib (n + 3) % 2 = Fib n % 2
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      -- Recurrence at index n+3: Fib (n+5) = Fib (n+4) + Fib (n+3).
      have h_lhs : Fib (n + 5) = Fib (n + 4) + Fib (n + 3) := by
        show Fib ((n + 3) + 2) = Fib (n + 4) + Fib (n + 3)
        rfl
      -- Recurrence at index n: Fib (n+2) = Fib (n+1) + Fib n.
      have h_rhs : Fib (n + 2) = Fib (n + 1) + Fib n := rfl
      -- IHs at n and n+1.
      have ih0 : Fib (n + 3) % 2 = Fib n % 2 := Fib_mod_2_period_3 n
      have ih1 : Fib ((n + 1) + 3) % 2 = Fib (n + 1) % 2 :=
        Fib_mod_2_period_3 (n + 1)
      have ih1' : Fib (n + 4) % 2 = Fib (n + 1) % 2 := ih1
      -- Reduce the LHS sum mod 2 via add_mod_gen.
      have h_lhs_mod : Fib (n + 5) % 2
          = ((Fib (n + 4) % 2) + (Fib (n + 3) % 2)) % 2 := by
        rw [h_lhs]; exact add_mod_gen (Fib (n + 4)) (Fib (n + 3)) 2
      have h_rhs_mod : Fib (n + 2) % 2
          = ((Fib (n + 1) % 2) + (Fib n % 2)) % 2 := by
        rw [h_rhs]; exact add_mod_gen (Fib (n + 1)) (Fib n) 2
      -- Substitute IHs.
      have h_swap : ((Fib (n + 4) % 2) + (Fib (n + 3) % 2)) % 2
                  = ((Fib (n + 1) % 2) + (Fib n % 2)) % 2 := by
        rw [ih0, ih1']
      -- Chain.
      show Fib ((n + 2) + 3) % 2 = Fib (n + 2) % 2
      have h_indices : (n + 2) + 3 = n + 5 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3 Mod-3 small table (decide-checked) -/

theorem Fib_0_mod_3  : Fib 0  % 3 = 0 := by decide
theorem Fib_1_mod_3  : Fib 1  % 3 = 1 := by decide
theorem Fib_8_mod_3  : Fib 8  % 3 = 0 := by decide
theorem Fib_9_mod_3  : Fib 9  % 3 = 1 := by decide
theorem Fib_10_mod_3 : Fib 10 % 3 = 1 := by decide

/-! ## §3' Period 8 mod 3 — parametric

2-step strong induction on `n`.  Base cases at `n ∈ {0, 1}`
verified by `decide`; inductive step at `n + 2` uses the
recurrence `Fib ((n+2) + 8) = Fib (n+10) = Fib (n+9) + Fib (n+8)`
combined with `Fib (n + 2) = Fib (n + 1) + Fib n`. -/

/-- ★ **Classical Pisano period 8 mod 3 for Fibonacci**:
    `Fib (n + 8) % 3 = Fib n % 3` for every `n : Nat`.

    Sister to the mod-2 period 3 result; same 2-step induction
    technique with modulus changed from 2 to 3. -/
theorem Fib_mod_3_period_8 : ∀ n, Fib (n + 8) % 3 = Fib n % 3
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Fib (n + 10) = Fib (n + 9) + Fib (n + 8) := by
        show Fib ((n + 8) + 2) = Fib (n + 9) + Fib (n + 8)
        rfl
      have h_rhs : Fib (n + 2) = Fib (n + 1) + Fib n := rfl
      have ih0 : Fib (n + 8) % 3 = Fib n % 3 := Fib_mod_3_period_8 n
      have ih1 : Fib ((n + 1) + 8) % 3 = Fib (n + 1) % 3 :=
        Fib_mod_3_period_8 (n + 1)
      have ih1' : Fib (n + 9) % 3 = Fib (n + 1) % 3 := ih1
      have h_lhs_mod : Fib (n + 10) % 3
          = ((Fib (n + 9) % 3) + (Fib (n + 8) % 3)) % 3 := by
        rw [h_lhs]; exact add_mod_gen (Fib (n + 9)) (Fib (n + 8)) 3
      have h_rhs_mod : Fib (n + 2) % 3
          = ((Fib (n + 1) % 3) + (Fib n % 3)) % 3 := by
        rw [h_rhs]; exact add_mod_gen (Fib (n + 1)) (Fib n) 3
      have h_swap : ((Fib (n + 9) % 3) + (Fib (n + 8) % 3)) % 3
                  = ((Fib (n + 1) % 3) + (Fib n % 3)) % 3 := by
        rw [ih0, ih1']
      show Fib ((n + 2) + 8) % 3 = Fib (n + 2) % 3
      have h_indices : (n + 2) + 8 = n + 10 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-- Period 8 mod 3 spot check: `Fib 8 % 3 = Fib 0 % 3`. -/
theorem Fib_8_eq_Fib_0_mod_3 : Fib 8 % 3 = Fib 0 % 3 := by decide

/-! ## §3'' Mod-5 period 20 — parametric

Classical Pisano π(5) = 20.  Same 2-step induction template;
larger base verification (decide must reach `Fib 21 = 10946`). -/

theorem Fib_0_mod_5  : Fib 0  % 5 = 0 := by decide
theorem Fib_1_mod_5  : Fib 1  % 5 = 1 := by decide
theorem Fib_20_mod_5 : Fib 20 % 5 = 0 := by decide
theorem Fib_21_mod_5 : Fib 21 % 5 = 1 := by decide

/-- ★ **Classical Pisano period 20 mod 5 for Fibonacci**:
    `Fib (n + 20) % 5 = Fib n % 5` for every `n : Nat`. -/
theorem Fib_mod_5_period_20 : ∀ n, Fib (n + 20) % 5 = Fib n % 5
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Fib (n + 22) = Fib (n + 21) + Fib (n + 20) := by
        show Fib ((n + 20) + 2) = Fib (n + 21) + Fib (n + 20)
        rfl
      have h_rhs : Fib (n + 2) = Fib (n + 1) + Fib n := rfl
      have ih0 : Fib (n + 20) % 5 = Fib n % 5 := Fib_mod_5_period_20 n
      have ih1 : Fib ((n + 1) + 20) % 5 = Fib (n + 1) % 5 :=
        Fib_mod_5_period_20 (n + 1)
      have ih1' : Fib (n + 21) % 5 = Fib (n + 1) % 5 := ih1
      have h_lhs_mod : Fib (n + 22) % 5
          = ((Fib (n + 21) % 5) + (Fib (n + 20) % 5)) % 5 := by
        rw [h_lhs]; exact add_mod_gen (Fib (n + 21)) (Fib (n + 20)) 5
      have h_rhs_mod : Fib (n + 2) % 5
          = ((Fib (n + 1) % 5) + (Fib n % 5)) % 5 := by
        rw [h_rhs]; exact add_mod_gen (Fib (n + 1)) (Fib n) 5
      have h_swap : ((Fib (n + 21) % 5) + (Fib (n + 20) % 5)) % 5
                  = ((Fib (n + 1) % 5) + (Fib n % 5)) % 5 := by
        rw [ih0, ih1']
      show Fib ((n + 2) + 20) % 5 = Fib (n + 2) % 5
      have h_indices : (n + 2) + 20 = n + 22 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3''' Mod-7 period 16 — parametric

Classical Pisano π(7) = 16.  Same 2-step induction template;
larger base verification (decide must reach `Fib 17 = 1597`). -/

theorem Fib_0_mod_7  : Fib 0  % 7 = 0 := by decide
theorem Fib_1_mod_7  : Fib 1  % 7 = 1 := by decide
theorem Fib_16_mod_7 : Fib 16 % 7 = 0 := by decide
theorem Fib_17_mod_7 : Fib 17 % 7 = 1 := by decide

/-- ★ **Classical Pisano period 16 mod 7 for Fibonacci**:
    `Fib (n + 16) % 7 = Fib n % 7` for every `n : Nat`. -/
theorem Fib_mod_7_period_16 : ∀ n, Fib (n + 16) % 7 = Fib n % 7
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Fib (n + 18) = Fib (n + 17) + Fib (n + 16) := by
        show Fib ((n + 16) + 2) = Fib (n + 17) + Fib (n + 16)
        rfl
      have h_rhs : Fib (n + 2) = Fib (n + 1) + Fib n := rfl
      have ih0 : Fib (n + 16) % 7 = Fib n % 7 := Fib_mod_7_period_16 n
      have ih1 : Fib ((n + 1) + 16) % 7 = Fib (n + 1) % 7 :=
        Fib_mod_7_period_16 (n + 1)
      have ih1' : Fib (n + 17) % 7 = Fib (n + 1) % 7 := ih1
      have h_lhs_mod : Fib (n + 18) % 7
          = ((Fib (n + 17) % 7) + (Fib (n + 16) % 7)) % 7 := by
        rw [h_lhs]; exact add_mod_gen (Fib (n + 17)) (Fib (n + 16)) 7
      have h_rhs_mod : Fib (n + 2) % 7
          = ((Fib (n + 1) % 7) + (Fib n % 7)) % 7 := by
        rw [h_rhs]; exact add_mod_gen (Fib (n + 1)) (Fib n) 7
      have h_swap : ((Fib (n + 17) % 7) + (Fib (n + 16) % 7)) % 7
                  = ((Fib (n + 1) % 7) + (Fib n % 7)) % 7 := by
        rw [ih0, ih1']
      show Fib ((n + 2) + 16) % 7 = Fib (n + 2) % 7
      have h_indices : (n + 2) + 16 = n + 18 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §4 Capstone -/

/-- ★★★ **Fibonacci modular-fingerprint capstone**.  Four
    parametric classical Pisano closures across the small-prime
    tetrad: π(2) = 3, π(3) = 8, π(5) = 20, π(7) = 16. -/
theorem capstone :
    (∀ n, Fib (n + 3) % 2 = Fib n % 2)
    ∧ (∀ n, Fib (n + 8) % 3 = Fib n % 3)
    ∧ (∀ n, Fib (n + 20) % 5 = Fib n % 5)
    ∧ (∀ n, Fib (n + 16) % 7 = Fib n % 7) :=
  ⟨Fib_mod_2_period_3, Fib_mod_3_period_8, Fib_mod_5_period_20,
   Fib_mod_7_period_16⟩

end E213.Lib.Math.Cohomology.Fractal.FibonacciModular
