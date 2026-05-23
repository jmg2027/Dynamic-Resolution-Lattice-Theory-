import E213.Lib.Math.Cohomology.Fractal.TribonacciCutoff
import E213.Meta.Nat.AddMod213

/-!
# Tribonacci-sequence modular fingerprint

Companion to `TribonacciCutoff.lean` — Pisano-period analogue for
the Tribonacci sequence.

The 3-step Tribonacci recurrence `T_{n+3} = T_{n+2} + T_{n+1} + T_n`
mod 2 has period 4 (orbit on the absorbing-free part of `2³ = 8`
mod-2 triples).  Decide-checked spot checks at the longer mod-3
period.

## Periods at small primes

| p | π_T(p) | first cycle (`T_0..T_{π−1} mod p`) |
|---|--------|------------------------------------|
| 2 | 4      | `0, 0, 1, 1` ★ parametric          |
| 3 | 13     | spot-checked                       |

## Why period 4 mod 2 is structural

The Tribonacci recurrence mod 2 is determined by the initial
triple `(T_0, T_1, T_2) = (0, 0, 1)` mod 2.  Among `2³ = 8`
mod-2 triples, the orbit starting at `(0, 0, 1)` cycles through 4
distinct triples and returns:

  · `(0, 0, 1) → (0, 1, 1) → (1, 1, 0) → (1, 0, 0) → (0, 0, 1)`

(reading windows of 3 consecutive values).  Hence π_T(2) = 4.
-/

namespace E213.Lib.Math.Cohomology.Fractal.TribonacciModular

open E213.Lib.Math.Cohomology.Fractal.TribonacciCutoff (Trib)
open E213.Meta.Nat.AddMod213

/-! ## §1 Mod-2 small table (decide-checked) -/

theorem Trib_0_mod_2  : Trib 0  % 2 = 0 := by decide
theorem Trib_1_mod_2  : Trib 1  % 2 = 0 := by decide
theorem Trib_2_mod_2  : Trib 2  % 2 = 1 := by decide
theorem Trib_3_mod_2  : Trib 3  % 2 = 1 := by decide
theorem Trib_4_mod_2  : Trib 4  % 2 = 0 := by decide
theorem Trib_5_mod_2  : Trib 5  % 2 = 0 := by decide
theorem Trib_6_mod_2  : Trib 6  % 2 = 1 := by decide
theorem Trib_7_mod_2  : Trib 7  % 2 = 1 := by decide
theorem Trib_8_mod_2  : Trib 8  % 2 = 0 := by decide

/-! ## §2 Period 4 mod 2 — parametric

3-step strong induction on `n`.  Base cases at `n ∈ {0, 1, 2}`
verified by `decide`; inductive step at `n + 3` uses the
recurrence `Trib ((n+3) + 4) = Trib (n+7) = Trib (n+6) +
Trib (n+5) + Trib (n+4)` combined with the matching
`Trib (n+3) = Trib (n+2) + Trib (n+1) + Trib n`. -/

/-- ★ **Period 4 mod 2 for Tribonacci**:
    `Trib (n + 4) % 2 = Trib n % 2` for every `n : Nat`.

    Pisano-period analogue: orbit on `2³ = 8` mod-2 triples
    starting at `(T_0, T_1, T_2) = (0, 0, 1)` cycles through 4
    distinct triples and returns. -/
theorem Trib_mod_2_period_4 : ∀ n, Trib (n + 4) % 2 = Trib n % 2
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      -- Recurrence at index n+4: Trib (n+7) = Trib (n+6) + Trib (n+5) + Trib (n+4).
      have h_lhs : Trib (n + 7) = Trib (n + 6) + Trib (n + 5) + Trib (n + 4) := by
        show Trib ((n + 4) + 3) = Trib (n + 6) + Trib (n + 5) + Trib (n + 4)
        rfl
      -- Recurrence at index n: Trib (n+3) = Trib (n+2) + Trib (n+1) + Trib n.
      have h_rhs : Trib (n + 3) = Trib (n + 2) + Trib (n + 1) + Trib n := rfl
      -- IHs at n, n+1, n+2.
      have ih0 : Trib (n + 4) % 2 = Trib n % 2 := Trib_mod_2_period_4 n
      have ih1 : Trib ((n + 1) + 4) % 2 = Trib (n + 1) % 2 :=
        Trib_mod_2_period_4 (n + 1)
      have ih2 : Trib ((n + 2) + 4) % 2 = Trib (n + 2) % 2 :=
        Trib_mod_2_period_4 (n + 2)
      have ih1' : Trib (n + 5) % 2 = Trib (n + 1) % 2 := ih1
      have ih2' : Trib (n + 6) % 2 = Trib (n + 2) % 2 := ih2
      -- Reduce the LHS triple sum mod 2 via successive add_mod_gen.
      have h_lhs_mod : Trib (n + 7) % 2
          = ((Trib (n + 6) + Trib (n + 5)) % 2 + (Trib (n + 4) % 2)) % 2 := by
        rw [h_lhs]
        exact add_mod_gen (Trib (n + 6) + Trib (n + 5)) (Trib (n + 4)) 2
      have h_lhs_mod' : (Trib (n + 6) + Trib (n + 5)) % 2
          = ((Trib (n + 6) % 2) + (Trib (n + 5) % 2)) % 2 :=
        add_mod_gen (Trib (n + 6)) (Trib (n + 5)) 2
      have h_rhs_mod : Trib (n + 3) % 2
          = ((Trib (n + 2) + Trib (n + 1)) % 2 + (Trib n % 2)) % 2 := by
        rw [h_rhs]
        exact add_mod_gen (Trib (n + 2) + Trib (n + 1)) (Trib n) 2
      have h_rhs_mod' : (Trib (n + 2) + Trib (n + 1)) % 2
          = ((Trib (n + 2) % 2) + (Trib (n + 1) % 2)) % 2 :=
        add_mod_gen (Trib (n + 2)) (Trib (n + 1)) 2
      -- Substitute IHs.
      have h_swap : ((Trib (n + 6) % 2) + (Trib (n + 5) % 2)) % 2
                  = ((Trib (n + 2) % 2) + (Trib (n + 1) % 2)) % 2 := by
        rw [ih1', ih2']
      -- Chain.
      show Trib ((n + 3) + 4) % 2 = Trib (n + 3) % 2
      have h_indices : (n + 3) + 4 = n + 7 := by rfl
      rw [h_indices, h_lhs_mod, h_lhs_mod', h_swap, ← h_rhs_mod', ih0, ← h_rhs_mod]

/-! ## §3 Mod-3 spot check (decide-checked) -/

theorem Trib_0_mod_3  : Trib 0  % 3 = 0 := by decide
theorem Trib_13_mod_3 : Trib 13 % 3 = 0 := by decide

/-- Period 13 mod 3 spot check: `Trib 13 % 3 = Trib 0 % 3`. -/
theorem Trib_13_eq_Trib_0_mod_3 : Trib 13 % 3 = Trib 0 % 3 := by decide

/-! ## §4 Capstone -/

/-- ★★★ **Tribonacci modular-fingerprint capstone**.  Records the
    parametric period-4 closure mod 2 alongside the decide-checked
    period-13 mod 3 spot check.  Sister to `PadovanModular.capstone`
    (Padovan: period 7 mod 2, period 13 mod 3, period 24 mod 5). -/
theorem capstone :
    -- Parametric period 4 mod 2
    (∀ n, Trib (n + 4) % 2 = Trib n % 2)
    -- Mod-3 period 13 spot check
    ∧ Trib 13 % 3 = Trib 0 % 3 :=
  ⟨Trib_mod_2_period_4, Trib_13_eq_Trib_0_mod_3⟩

end E213.Lib.Math.Cohomology.Fractal.TribonacciModular
