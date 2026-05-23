import E213.Lib.Math.Cohomology.Fractal.LucasCutoff
import E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff
import E213.Meta.Nat.AddMod213

/-!
# Lucas-sequence modular fingerprint

Companion to `LucasCutoff.lean` — Pisano-period analogue for the
Lucas sequence.  Lucas and Fibonacci share the recurrence
`x_{n+2} = x_{n+1} + x_n` but with different initial conditions:
`(L_0, L_1) = (2, 1)` vs. `(F_0, F_1) = (0, 1)`.

Mod 2, the initial pair `(L_0, L_1) = (0, 1)` coincides with
`(F_0, F_1)`, so Lucas and Fibonacci share the same mod-2 orbit
and therefore the same Pisano period `π(2) = 3`.  Mod 3 the
orbits diverge: Lucas has period 8 vs. Fibonacci's period 8 (the
orbit landings differ; spot-check ships `L_8 % 3 = L_0 % 3`).

## Periods at small primes

| p | π_L(p) | first cycle (`L_0..L_{π−1} mod p`) |
|---|--------|------------------------------------|
| 2 | 3      | `0, 1, 1` ★ parametric (shared with Fibonacci) |
| 3 | 8      | spot-checked                       |

## Why Lucas and Fibonacci share π(2) = 3

The mod-2 Pisano period is determined by the orbit on `2² = 4`
mod-2 pairs starting at the reduced initial pair.  Both Lucas
`(L_0, L_1) = (2, 1) ≡ (0, 1) mod 2` and Fibonacci
`(F_0, F_1) = (0, 1)` land on the same initial pair after
mod-2 reduction.  The shared recurrence then generates an
identical mod-2 orbit `(0, 1) → (1, 1) → (1, 0) → (0, 1)`,
yielding `π_L(2) = π_F(2) = 3`.

The mod-3 orbits diverge because the reduced initial pairs are
distinct: `(L_0, L_1) ≡ (2, 1) mod 3` vs.
`(F_0, F_1) ≡ (0, 1) mod 3`.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Fractal.LucasModular

open E213.Lib.Math.Cohomology.Fractal.LucasCutoff (Lucas)
open E213.Meta.Nat.AddMod213

/-! ## §1 Mod-2 small table (decide-checked) -/

theorem Lucas_0_mod_2  : Lucas 0  % 2 = 0 := by decide
theorem Lucas_1_mod_2  : Lucas 1  % 2 = 1 := by decide
theorem Lucas_2_mod_2  : Lucas 2  % 2 = 1 := by decide
theorem Lucas_3_mod_2  : Lucas 3  % 2 = 0 := by decide
theorem Lucas_4_mod_2  : Lucas 4  % 2 = 1 := by decide
theorem Lucas_5_mod_2  : Lucas 5  % 2 = 1 := by decide
theorem Lucas_6_mod_2  : Lucas 6  % 2 = 0 := by decide

/-! ## §2 Period 3 mod 2 — parametric

2-step strong induction on `n`.  Base cases at `n ∈ {0, 1}`
verified by `decide`; inductive step at `n + 2` uses the
recurrence `Lucas ((n+2) + 3) = Lucas (n+5)
= Lucas (n+4) + Lucas (n+3)` combined with the matching
`Lucas (n+2) = Lucas (n+1) + Lucas n`.

Mirrors `FibonacciModular.Fib_mod_2_period_3` (same recurrence,
same period; only the initial pair differs but reduces to the
same mod-2 pair). -/

/-- ★ **Pisano period 3 mod 2 for Lucas**:
    `Lucas (n + 3) % 2 = Lucas n % 2` for every `n : Nat`.

    Shared orbit with Fibonacci (same recurrence + reduced
    initial pair `(0, 1)`). -/
theorem Lucas_mod_2_period_3 : ∀ n, Lucas (n + 3) % 2 = Lucas n % 2
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      -- Recurrence at index n+3: Lucas (n+5) = Lucas (n+4) + Lucas (n+3).
      have h_lhs : Lucas (n + 5) = Lucas (n + 4) + Lucas (n + 3) := by
        show Lucas ((n + 3) + 2) = Lucas (n + 4) + Lucas (n + 3)
        rfl
      -- Recurrence at index n: Lucas (n+2) = Lucas (n+1) + Lucas n.
      have h_rhs : Lucas (n + 2) = Lucas (n + 1) + Lucas n := rfl
      -- IHs at n and n+1.
      have ih0 : Lucas (n + 3) % 2 = Lucas n % 2 := Lucas_mod_2_period_3 n
      have ih1 : Lucas ((n + 1) + 3) % 2 = Lucas (n + 1) % 2 :=
        Lucas_mod_2_period_3 (n + 1)
      have ih1' : Lucas (n + 4) % 2 = Lucas (n + 1) % 2 := ih1
      -- Reduce the LHS sum mod 2 via add_mod_gen.
      have h_lhs_mod : Lucas (n + 5) % 2
          = ((Lucas (n + 4) % 2) + (Lucas (n + 3) % 2)) % 2 := by
        rw [h_lhs]; exact add_mod_gen (Lucas (n + 4)) (Lucas (n + 3)) 2
      have h_rhs_mod : Lucas (n + 2) % 2
          = ((Lucas (n + 1) % 2) + (Lucas n % 2)) % 2 := by
        rw [h_rhs]; exact add_mod_gen (Lucas (n + 1)) (Lucas n) 2
      -- Substitute IHs.
      have h_swap : ((Lucas (n + 4) % 2) + (Lucas (n + 3) % 2)) % 2
                  = ((Lucas (n + 1) % 2) + (Lucas n % 2)) % 2 := by
        rw [ih0, ih1']
      -- Chain.
      show Lucas ((n + 2) + 3) % 2 = Lucas (n + 2) % 2
      have h_indices : (n + 2) + 3 = n + 5 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3 Mod-3 small table (decide-checked) -/

theorem Lucas_0_mod_3  : Lucas 0  % 3 = 2 := by decide
theorem Lucas_1_mod_3  : Lucas 1  % 3 = 1 := by decide
theorem Lucas_8_mod_3  : Lucas 8  % 3 = 2 := by decide
theorem Lucas_9_mod_3  : Lucas 9  % 3 = 1 := by decide
theorem Lucas_10_mod_3 : Lucas 10 % 3 = 0 := by decide

/-! ## §3' Period 8 mod 3 — parametric

Same recurrence as Fibonacci with different initial pair
`(L_0, L_1) ≡ (2, 1) mod 3`.  Same period (8) but distinct
mod-3 orbit (`2, 1, 0, 1, 1, 2, 0, 2` vs. Fibonacci's
`0, 1, 1, 2, 0, 2, 2, 1`).  2-step induction template
identical to `FibonacciModular.Fib_mod_3_period_8`. -/

/-- ★ **Pisano period 8 mod 3 for Lucas**:
    `Lucas (n + 8) % 3 = Lucas n % 3` for every `n : Nat`.

    Same period as Fibonacci mod 3 (shared recurrence) but
    different orbit landings (distinct reduced initial pair). -/
theorem Lucas_mod_3_period_8 : ∀ n, Lucas (n + 8) % 3 = Lucas n % 3
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Lucas (n + 10) = Lucas (n + 9) + Lucas (n + 8) := by
        show Lucas ((n + 8) + 2) = Lucas (n + 9) + Lucas (n + 8)
        rfl
      have h_rhs : Lucas (n + 2) = Lucas (n + 1) + Lucas n := rfl
      have ih0 : Lucas (n + 8) % 3 = Lucas n % 3 := Lucas_mod_3_period_8 n
      have ih1 : Lucas ((n + 1) + 8) % 3 = Lucas (n + 1) % 3 :=
        Lucas_mod_3_period_8 (n + 1)
      have ih1' : Lucas (n + 9) % 3 = Lucas (n + 1) % 3 := ih1
      have h_lhs_mod : Lucas (n + 10) % 3
          = ((Lucas (n + 9) % 3) + (Lucas (n + 8) % 3)) % 3 := by
        rw [h_lhs]; exact add_mod_gen (Lucas (n + 9)) (Lucas (n + 8)) 3
      have h_rhs_mod : Lucas (n + 2) % 3
          = ((Lucas (n + 1) % 3) + (Lucas n % 3)) % 3 := by
        rw [h_rhs]; exact add_mod_gen (Lucas (n + 1)) (Lucas n) 3
      have h_swap : ((Lucas (n + 9) % 3) + (Lucas (n + 8) % 3)) % 3
                  = ((Lucas (n + 1) % 3) + (Lucas n % 3)) % 3 := by
        rw [ih0, ih1']
      show Lucas ((n + 2) + 8) % 3 = Lucas (n + 2) % 3
      have h_indices : (n + 2) + 8 = n + 10 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-- Period 8 mod 3 spot check: `Lucas 8 % 3 = Lucas 0 % 3`. -/
theorem Lucas_8_eq_Lucas_0_mod_3 : Lucas 8 % 3 = Lucas 0 % 3 := by decide

/-! ## §3'' Mod-5 period 4 — parametric

Lucas mod 5 cycles through `(2, 1, 3, 4)`, only 4 distinct
values — shortest period in the family among the small primes.
Same 2-step induction template; only 2 base cases needed. -/

theorem Lucas_0_mod_5  : Lucas 0  % 5 = 2 := by decide
theorem Lucas_1_mod_5  : Lucas 1  % 5 = 1 := by decide
theorem Lucas_4_mod_5  : Lucas 4  % 5 = 2 := by decide
theorem Lucas_5_mod_5  : Lucas 5  % 5 = 1 := by decide

/-- ★ **Period 4 mod 5 for Lucas**:
    `Lucas (n + 4) % 5 = Lucas n % 5` for every `n : Nat`.

    Cycle `(2, 1, 3, 4)` — 4 distinct values, shortest among
    Lucas Pisano periods at small primes (mod 2 has period 3,
    mod 3 has period 8). -/
theorem Lucas_mod_5_period_4 : ∀ n, Lucas (n + 4) % 5 = Lucas n % 5
  | 0     => by decide
  | 1     => by decide
  | n + 2 => by
      have h_lhs : Lucas (n + 6) = Lucas (n + 5) + Lucas (n + 4) := by
        show Lucas ((n + 4) + 2) = Lucas (n + 5) + Lucas (n + 4)
        rfl
      have h_rhs : Lucas (n + 2) = Lucas (n + 1) + Lucas n := rfl
      have ih0 : Lucas (n + 4) % 5 = Lucas n % 5 := Lucas_mod_5_period_4 n
      have ih1 : Lucas ((n + 1) + 4) % 5 = Lucas (n + 1) % 5 :=
        Lucas_mod_5_period_4 (n + 1)
      have ih1' : Lucas (n + 5) % 5 = Lucas (n + 1) % 5 := ih1
      have h_lhs_mod : Lucas (n + 6) % 5
          = ((Lucas (n + 5) % 5) + (Lucas (n + 4) % 5)) % 5 := by
        rw [h_lhs]; exact add_mod_gen (Lucas (n + 5)) (Lucas (n + 4)) 5
      have h_rhs_mod : Lucas (n + 2) % 5
          = ((Lucas (n + 1) % 5) + (Lucas n % 5)) % 5 := by
        rw [h_rhs]; exact add_mod_gen (Lucas (n + 1)) (Lucas n) 5
      have h_swap : ((Lucas (n + 5) % 5) + (Lucas (n + 4) % 5)) % 5
                  = ((Lucas (n + 1) % 5) + (Lucas n % 5)) % 5 := by
        rw [ih0, ih1']
      show Lucas ((n + 2) + 4) % 5 = Lucas (n + 2) % 5
      have h_indices : (n + 2) + 4 = n + 6 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §4 Cross-sequence sharing — Fibonacci ↔ Lucas mod-2

Both `Fib` and `Lucas` satisfy `x_{n+2} = x_{n+1} + x_n` with
reduced mod-2 initial pair `(0, 1)`, hence identical mod-2
orbits.  The shared-period identity is recorded as a structural
spot-check. -/

/-- ★ **Mod-2 cycle sharing**: `Lucas n % 2 = Fib n % 2` for the
    first cycle period (`n < 3`).  Sister identity reflecting
    the shared mod-2 orbit. -/
theorem Lucas_mod_2_eq_Fib_mod_2_first_cycle :
    Lucas 0 % 2 = E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff.Fib 0 % 2
    ∧ Lucas 1 % 2 = E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff.Fib 1 % 2
    ∧ Lucas 2 % 2 = E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff.Fib 2 % 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5 Capstone -/

/-- ★★★ **Lucas modular-fingerprint capstone**.  Three parametric
    Pisano closures: period 3 mod 2, period 8 mod 3, period 4
    mod 5 — shortest period in the small-prime triplet.
    Decide-checked mod-2 cycle sharing with Fibonacci on the
    first cycle. -/
theorem capstone :
    -- Parametric period 3 mod 2 (shared with Fibonacci)
    (∀ n, Lucas (n + 3) % 2 = Lucas n % 2)
    -- Parametric period 8 mod 3
    ∧ (∀ n, Lucas (n + 8) % 3 = Lucas n % 3)
    -- Parametric period 4 mod 5
    ∧ (∀ n, Lucas (n + 4) % 5 = Lucas n % 5)
    -- Cycle sharing with Fibonacci
    ∧ (Lucas 0 % 2 = E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff.Fib 0 % 2
       ∧ Lucas 1 % 2 = E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff.Fib 1 % 2
       ∧ Lucas 2 % 2 = E213.Lib.Math.Cohomology.Fractal.FibonacciCutoff.Fib 2 % 2) :=
  ⟨Lucas_mod_2_period_3, Lucas_mod_3_period_8, Lucas_mod_5_period_4,
   Lucas_mod_2_eq_Fib_mod_2_first_cycle⟩

end E213.Lib.Math.Cohomology.Fractal.LucasModular
