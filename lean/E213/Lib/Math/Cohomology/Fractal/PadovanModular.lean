import E213.Lib.Math.Cohomology.Fractal.PadovanCutoff
import E213.Meta.Nat.AddMod213

/-!
# Padovan-sequence modular fingerprint

Companion to `PadovanCutoff.lean` — explores `Pad n % p` for small
primes `p`, paralleling `ConfigCountModular.lean` for the
`configCountD 5 n` family.

Padovan sequence `P_{n+3} = P_{n+1} + P_n` admits a clean
Pisano-period analogue ("Padovan period" π_P(p)) for each prime
`p`.  The mod-2 case is closed parametrically below with period
7; mod-3 and mod-5 cases have decide-checked tables with
periods 13 and 24 respectively.

## Periods at small primes

| p | π_P(p) | first cycle (`P_0..P_{π−1} mod p`)             |
|---|--------|------------------------------------------------|
| 2 | 7      | `1, 1, 1, 0, 0, 1, 0` ★ parametric             |
| 3 | 13     | `1, 1, 1, 2, 2, 0, 1, 2, 1, 0, 0, 1, 0` table  |
| 5 | 24     | `1, 1, 1, 2, 2, 3, 4, 0, 2, 4, 2, 1, 1, 3, 2, 4, 0, 1, 4, 1, 0, 0, 1, 0` |

## Why period 7 mod 2 is structural

The 3-step Padovan recurrence is determined by the initial triple
`(P_n, P_{n+1}, P_{n+2})` mod 2.  Among `2³ = 8` possible
mod-2 triples, the orbit starting at `(1, 1, 1)` visits 7
distinct triples and then returns — the (0, 0, 0) absorbing
triple is not on the orbit.  Hence π_P(2) = 7.
-/

namespace E213.Lib.Math.Cohomology.Fractal.PadovanModular

open E213.Lib.Math.Cohomology.Fractal.PadovanCutoff (Pad)
open E213.Meta.Nat.AddMod213

/-! ## §1 Mod-2 small table (decide-checked) -/

theorem Pad_0_mod_2  : Pad 0  % 2 = 1 := by decide
theorem Pad_1_mod_2  : Pad 1  % 2 = 1 := by decide
theorem Pad_2_mod_2  : Pad 2  % 2 = 1 := by decide
theorem Pad_3_mod_2  : Pad 3  % 2 = 0 := by decide
theorem Pad_4_mod_2  : Pad 4  % 2 = 0 := by decide
theorem Pad_5_mod_2  : Pad 5  % 2 = 1 := by decide
theorem Pad_6_mod_2  : Pad 6  % 2 = 0 := by decide
theorem Pad_7_mod_2  : Pad 7  % 2 = 1 := by decide
theorem Pad_8_mod_2  : Pad 8  % 2 = 1 := by decide
theorem Pad_9_mod_2  : Pad 9  % 2 = 1 := by decide
theorem Pad_13_mod_2 : Pad 13 % 2 = 0 := by decide

/-! ## §2 Period 7 mod 2 — parametric

3-step strong induction on `n`.  Base cases at `n ∈ {0, 1, 2}`
verified by `decide` over Padovan values at indices `≤ 9`.
Inductive step at `n + 3` uses the recurrence
`Pad ((n+3) + 7) = Pad (n + 10) = Pad (n + 8) + Pad (n + 7)`
combined with the matching `Pad (n + 3) = Pad (n + 1) + Pad n`. -/

/-- ★ **Period 7 mod 2 for Padovan**: `Pad (n + 7) % 2 = Pad n % 2`
    for every `n : Nat`.

    Pisano-period analogue: among the `2³ = 8` mod-2 triples, the
    orbit starting at `(P_0, P_1, P_2) = (1, 1, 1)` mod 2 cycles
    through 7 distinct triples and returns. -/
theorem Pad_mod_2_period_7 : ∀ n, Pad (n + 7) % 2 = Pad n % 2
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      -- `Pad ((n+3) + 7) = Pad (n+10) = Pad (n+8) + Pad (n+7)` by
      -- the recurrence at index `n+7` (i.e. `Pad ((n+7)+3)`).
      have h_lhs : Pad (n + 10) = Pad (n + 8) + Pad (n + 7) := by
        show Pad ((n + 7) + 3) = Pad (n + 8) + Pad (n + 7)
        rfl
      -- `Pad (n+3) = Pad (n+1) + Pad n` by the recurrence at `n`.
      have h_rhs : Pad (n + 3) = Pad (n + 1) + Pad n := rfl
      -- IH at `n` and `n+1`.
      have ih0 : Pad (n + 7) % 2 = Pad n % 2 :=
        Pad_mod_2_period_7 n
      have ih1 : Pad ((n + 1) + 7) % 2 = Pad (n + 1) % 2 :=
        Pad_mod_2_period_7 (n + 1)
      -- Unfold `(n+1)+7 = n+8` in `ih1`.
      have ih1' : Pad (n + 8) % 2 = Pad (n + 1) % 2 := ih1
      -- Reduce the LHS sum mod 2 via add_mod_gen.
      have h_lhs_mod : Pad (n + 10) % 2
          = ((Pad (n + 8) % 2) + (Pad (n + 7) % 2)) % 2 := by
        rw [h_lhs]; exact add_mod_gen (Pad (n + 8)) (Pad (n + 7)) 2
      have h_rhs_mod : Pad (n + 3) % 2
          = ((Pad (n + 1) % 2) + (Pad n % 2)) % 2 := by
        rw [h_rhs]; exact add_mod_gen (Pad (n + 1)) (Pad n) 2
      -- Substitute IHs into the LHS expression.
      have h_swap : ((Pad (n + 8) % 2) + (Pad (n + 7) % 2)) % 2
                  = ((Pad (n + 1) % 2) + (Pad n % 2)) % 2 := by
        rw [ih0, ih1']
      -- Chain.
      show Pad ((n + 3) + 7) % 2 = Pad (n + 3) % 2
      have h_indices : (n + 3) + 7 = n + 10 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3 Mod-3 small table (decide-checked) -/

theorem Pad_0_mod_3  : Pad 0  % 3 = 1 := by decide
theorem Pad_3_mod_3  : Pad 3  % 3 = 2 := by decide
theorem Pad_5_mod_3  : Pad 5  % 3 = 0 := by decide
theorem Pad_8_mod_3  : Pad 8  % 3 = 1 := by decide
theorem Pad_13_mod_3 : Pad 13 % 3 = 1 := by decide
theorem Pad_14_mod_3 : Pad 14 % 3 = 1 := by decide
theorem Pad_15_mod_3 : Pad 15 % 3 = 1 := by decide

/-! ## §3' Period 13 mod 3 — parametric

3-step strong induction on `n`.  Base cases at `n ∈ {0, 1, 2}`
verified by `decide` over Padovan values at indices `≤ 15`;
inductive step at `n + 3` uses the recurrence
`Pad ((n+3) + 13) = Pad (n + 16) = Pad (n + 14) + Pad (n + 13)`
combined with the matching `Pad (n + 3) = Pad (n + 1) + Pad n`.

Sister to `Pad_mod_2_period_7`; same nested-induction technique
with the modulus changed from 2 to 3. -/

/-- ★ **Period 13 mod 3 for Padovan**:
    `Pad (n + 13) % 3 = Pad n % 3` for every `n : Nat`.

    Pisano-period analogue: the mod-3 orbit on `3³ = 27` triples
    cycles through 13 distinct states before returning. -/
theorem Pad_mod_3_period_13 : ∀ n, Pad (n + 13) % 3 = Pad n % 3
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      have h_lhs : Pad (n + 16) = Pad (n + 14) + Pad (n + 13) := by
        show Pad ((n + 13) + 3) = Pad (n + 14) + Pad (n + 13)
        rfl
      have h_rhs : Pad (n + 3) = Pad (n + 1) + Pad n := rfl
      have ih0 : Pad (n + 13) % 3 = Pad n % 3 := Pad_mod_3_period_13 n
      have ih1 : Pad ((n + 1) + 13) % 3 = Pad (n + 1) % 3 :=
        Pad_mod_3_period_13 (n + 1)
      have ih1' : Pad (n + 14) % 3 = Pad (n + 1) % 3 := ih1
      have h_lhs_mod : Pad (n + 16) % 3
          = ((Pad (n + 14) % 3) + (Pad (n + 13) % 3)) % 3 := by
        rw [h_lhs]; exact add_mod_gen (Pad (n + 14)) (Pad (n + 13)) 3
      have h_rhs_mod : Pad (n + 3) % 3
          = ((Pad (n + 1) % 3) + (Pad n % 3)) % 3 := by
        rw [h_rhs]; exact add_mod_gen (Pad (n + 1)) (Pad n) 3
      have h_swap : ((Pad (n + 14) % 3) + (Pad (n + 13) % 3)) % 3
                  = ((Pad (n + 1) % 3) + (Pad n % 3)) % 3 := by
        rw [ih0, ih1']
      show Pad ((n + 3) + 13) % 3 = Pad (n + 3) % 3
      have h_indices : (n + 3) + 13 = n + 16 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-- Period 13 mod 3 spot check: `Pad 13 % 3 = Pad 0 % 3`. -/
theorem Pad_13_eq_Pad_0_mod_3 : Pad 13 % 3 = Pad 0 % 3 := by decide

/-! ## §4 Mod-5 small table (decide-checked) -/

theorem Pad_0_mod_5  : Pad 0  % 5 = 1 := by decide
theorem Pad_7_mod_5  : Pad 7  % 5 = 0 := by decide
theorem Pad_24_mod_5 : Pad 24 % 5 = 1 := by decide

/-- Period 24 mod 5 spot check: `Pad 24 % 5 = Pad 0 % 5`. -/
theorem Pad_24_eq_Pad_0_mod_5 : Pad 24 % 5 = Pad 0 % 5 := by decide

/-! ## §5 Capstone -/

/-- ★★★ **Padovan modular-fingerprint capstone**.  Two parametric
    Pisano-analogue closures (period 7 mod 2 + period 13 mod 3)
    alongside decide-checked period-24 mod 5 spot check. -/
theorem capstone :
    -- Parametric period 7 mod 2
    (∀ n, Pad (n + 7) % 2 = Pad n % 2)
    -- Parametric period 13 mod 3
    ∧ (∀ n, Pad (n + 13) % 3 = Pad n % 3)
    -- Mod-5 period 24 spot check
    ∧ Pad 24 % 5 = Pad 0 % 5 :=
  ⟨Pad_mod_2_period_7, Pad_mod_3_period_13, Pad_24_eq_Pad_0_mod_5⟩

end E213.Lib.Math.Cohomology.Fractal.PadovanModular
