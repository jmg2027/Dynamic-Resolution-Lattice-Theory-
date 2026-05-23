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

/-! ## §3 Mod-3 small table (decide-checked) -/

theorem Trib_0_mod_3  : Trib 0  % 3 = 0 := by decide
theorem Trib_1_mod_3  : Trib 1  % 3 = 0 := by decide
theorem Trib_2_mod_3  : Trib 2  % 3 = 1 := by decide
theorem Trib_13_mod_3 : Trib 13 % 3 = 0 := by decide
theorem Trib_14_mod_3 : Trib 14 % 3 = 0 := by decide
theorem Trib_15_mod_3 : Trib 15 % 3 = 1 := by decide

/-! ## §3' Period 13 mod 3 — parametric

3-step strong induction on `n`.  Base cases at `n ∈ {0, 1, 2}`
verified by `decide`; inductive step at `n + 3` uses the
recurrence `Trib ((n+3) + 13) = Trib (n+16) = Trib (n+15)
+ Trib (n+14) + Trib (n+13)` combined with
`Trib (n + 3) = Trib (n + 2) + Trib (n + 1) + Trib n`. -/

/-- ★ **Period 13 mod 3 for Tribonacci**:
    `Trib (n + 13) % 3 = Trib n % 3` for every `n : Nat`.

    Sister to the mod-2 period 4 result; same 3-step induction
    technique with the modulus changed from 2 to 3 and the
    period from 4 to 13. -/
theorem Trib_mod_3_period_13 : ∀ n, Trib (n + 13) % 3 = Trib n % 3
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      have h_lhs : Trib (n + 16) = Trib (n + 15) + Trib (n + 14) + Trib (n + 13) := by
        show Trib ((n + 13) + 3) = Trib (n + 15) + Trib (n + 14) + Trib (n + 13)
        rfl
      have h_rhs : Trib (n + 3) = Trib (n + 2) + Trib (n + 1) + Trib n := rfl
      have ih0 : Trib (n + 13) % 3 = Trib n % 3 := Trib_mod_3_period_13 n
      have ih1 : Trib ((n + 1) + 13) % 3 = Trib (n + 1) % 3 :=
        Trib_mod_3_period_13 (n + 1)
      have ih2 : Trib ((n + 2) + 13) % 3 = Trib (n + 2) % 3 :=
        Trib_mod_3_period_13 (n + 2)
      have ih1' : Trib (n + 14) % 3 = Trib (n + 1) % 3 := ih1
      have ih2' : Trib (n + 15) % 3 = Trib (n + 2) % 3 := ih2
      have h_lhs_mod : Trib (n + 16) % 3
          = ((Trib (n + 15) + Trib (n + 14)) % 3 + (Trib (n + 13) % 3)) % 3 := by
        rw [h_lhs]
        exact add_mod_gen (Trib (n + 15) + Trib (n + 14)) (Trib (n + 13)) 3
      have h_lhs_mod' : (Trib (n + 15) + Trib (n + 14)) % 3
          = ((Trib (n + 15) % 3) + (Trib (n + 14) % 3)) % 3 :=
        add_mod_gen (Trib (n + 15)) (Trib (n + 14)) 3
      have h_rhs_mod : Trib (n + 3) % 3
          = ((Trib (n + 2) + Trib (n + 1)) % 3 + (Trib n % 3)) % 3 := by
        rw [h_rhs]
        exact add_mod_gen (Trib (n + 2) + Trib (n + 1)) (Trib n) 3
      have h_rhs_mod' : (Trib (n + 2) + Trib (n + 1)) % 3
          = ((Trib (n + 2) % 3) + (Trib (n + 1) % 3)) % 3 :=
        add_mod_gen (Trib (n + 2)) (Trib (n + 1)) 3
      have h_swap : ((Trib (n + 15) % 3) + (Trib (n + 14) % 3)) % 3
                  = ((Trib (n + 2) % 3) + (Trib (n + 1) % 3)) % 3 := by
        rw [ih1', ih2']
      show Trib ((n + 3) + 13) % 3 = Trib (n + 3) % 3
      have h_indices : (n + 3) + 13 = n + 16 := by rfl
      rw [h_indices, h_lhs_mod, h_lhs_mod', h_swap, ← h_rhs_mod', ih0, ← h_rhs_mod]

/-- Period 13 mod 3 spot check: `Trib 13 % 3 = Trib 0 % 3`. -/
theorem Trib_13_eq_Trib_0_mod_3 : Trib 13 % 3 = Trib 0 % 3 := by decide

/-! ## §4 Capstone -/

/-- ★★★ **Tribonacci modular-fingerprint capstone**.  Two
    parametric Pisano closures: period 4 mod 2 + period 13 mod 3.
    Sister to `PadovanModular.capstone` (period 7 mod 2 + period
    13 mod 3 + period 24 mod 5 parametric). -/
theorem capstone_2_3 :
    -- Parametric period 4 mod 2
    (∀ n, Trib (n + 4) % 2 = Trib n % 2)
    -- Parametric period 13 mod 3
    ∧ (∀ n, Trib (n + 13) % 3 = Trib n % 3) :=
  ⟨Trib_mod_2_period_4, Trib_mod_3_period_13⟩

/-! ## §5 Mod-5 period 31 — parametric (deferred-no-longer)

Tribonacci mod 5 has period 31 — same as Narayana mod 5, despite
different recurrences.  3-step nested induction with 3 IH terms
(`n`, `n+1`, `n+2`); base cases at `n ∈ {0, 1, 2}` verified by
`decide` over Tribonacci values at indices `≤ 33` (≈ 1.8 × 10⁸).
Triple-`add_mod_gen` modular sum reduction. -/

theorem Trib_0_mod_5  : Trib 0  % 5 = 0 := by decide
theorem Trib_1_mod_5  : Trib 1  % 5 = 0 := by decide
theorem Trib_2_mod_5  : Trib 2  % 5 = 1 := by decide
theorem Trib_31_mod_5 : Trib 31 % 5 = 0 := by decide
theorem Trib_32_mod_5 : Trib 32 % 5 = 0 := by decide
theorem Trib_33_mod_5 : Trib 33 % 5 = 1 := by decide

/-- ★ **Period 31 mod 5 for Tribonacci**:
    `Trib (n + 31) % 5 = Trib n % 5` for every `n : Nat`.

    Twin to `NarayanaModular.Nara_mod_5_period_31` (same period
    31 despite different recurrences).  3-step nested induction
    + triple `add_mod_gen` for the 3-term recurrence reduction. -/
theorem Trib_mod_5_period_31 : ∀ n, Trib (n + 31) % 5 = Trib n % 5
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      have h_lhs : Trib (n + 34)
                 = Trib (n + 33) + Trib (n + 32) + Trib (n + 31) := by
        show Trib ((n + 31) + 3)
           = Trib (n + 33) + Trib (n + 32) + Trib (n + 31)
        rfl
      have h_rhs : Trib (n + 3) = Trib (n + 2) + Trib (n + 1) + Trib n := rfl
      have ih0 : Trib (n + 31) % 5 = Trib n % 5 := Trib_mod_5_period_31 n
      have ih1 : Trib ((n + 1) + 31) % 5 = Trib (n + 1) % 5 :=
        Trib_mod_5_period_31 (n + 1)
      have ih2 : Trib ((n + 2) + 31) % 5 = Trib (n + 2) % 5 :=
        Trib_mod_5_period_31 (n + 2)
      have ih1' : Trib (n + 32) % 5 = Trib (n + 1) % 5 := ih1
      have ih2' : Trib (n + 33) % 5 = Trib (n + 2) % 5 := ih2
      have h_lhs_mod : Trib (n + 34) % 5
          = ((Trib (n + 33) + Trib (n + 32)) % 5 + (Trib (n + 31) % 5)) % 5 := by
        rw [h_lhs]
        exact add_mod_gen (Trib (n + 33) + Trib (n + 32)) (Trib (n + 31)) 5
      have h_lhs_mod' : (Trib (n + 33) + Trib (n + 32)) % 5
          = ((Trib (n + 33) % 5) + (Trib (n + 32) % 5)) % 5 :=
        add_mod_gen (Trib (n + 33)) (Trib (n + 32)) 5
      have h_rhs_mod : Trib (n + 3) % 5
          = ((Trib (n + 2) + Trib (n + 1)) % 5 + (Trib n % 5)) % 5 := by
        rw [h_rhs]
        exact add_mod_gen (Trib (n + 2) + Trib (n + 1)) (Trib n) 5
      have h_rhs_mod' : (Trib (n + 2) + Trib (n + 1)) % 5
          = ((Trib (n + 2) % 5) + (Trib (n + 1) % 5)) % 5 :=
        add_mod_gen (Trib (n + 2)) (Trib (n + 1)) 5
      have h_swap : ((Trib (n + 33) % 5) + (Trib (n + 32) % 5)) % 5
                  = ((Trib (n + 2) % 5) + (Trib (n + 1) % 5)) % 5 := by
        rw [ih1', ih2']
      show Trib ((n + 3) + 31) % 5 = Trib (n + 3) % 5
      have h_indices : (n + 3) + 31 = n + 34 := by rfl
      rw [h_indices, h_lhs_mod, h_lhs_mod', h_swap, ← h_rhs_mod', ih0, ← h_rhs_mod]

/-! ## §6 Period 48 mod 7 — parametric

Same period (48) as Padovan mod 7 — structural twin via the
mod-7 modular layer despite different recurrences.  3-step
recurrence with 3 IH terms; base values at indices 48-50 are
~10¹² (decide handles via Nat). -/

theorem Trib_48_mod_7 : Trib 48 % 7 = 0 := by decide
theorem Trib_49_mod_7 : Trib 49 % 7 = 0 := by decide
theorem Trib_50_mod_7 : Trib 50 % 7 = 1 := by decide

/-- ★ **Period 48 mod 7 for Tribonacci**:
    `Trib (n + 48) % 7 = Trib n % 7` for every `n : Nat`.

    ★ STRUCTURAL TWIN with Padovan mod 7 (both period 48). -/
theorem Trib_mod_7_period_48 : ∀ n, Trib (n + 48) % 7 = Trib n % 7
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      have h_lhs : Trib (n + 51)
                 = Trib (n + 50) + Trib (n + 49) + Trib (n + 48) := by
        show Trib ((n + 48) + 3)
           = Trib (n + 50) + Trib (n + 49) + Trib (n + 48)
        rfl
      have h_rhs : Trib (n + 3) = Trib (n + 2) + Trib (n + 1) + Trib n := rfl
      have ih0 : Trib (n + 48) % 7 = Trib n % 7 := Trib_mod_7_period_48 n
      have ih1 : Trib ((n + 1) + 48) % 7 = Trib (n + 1) % 7 :=
        Trib_mod_7_period_48 (n + 1)
      have ih2 : Trib ((n + 2) + 48) % 7 = Trib (n + 2) % 7 :=
        Trib_mod_7_period_48 (n + 2)
      have ih1' : Trib (n + 49) % 7 = Trib (n + 1) % 7 := ih1
      have ih2' : Trib (n + 50) % 7 = Trib (n + 2) % 7 := ih2
      have h_lhs_mod : Trib (n + 51) % 7
          = ((Trib (n + 50) + Trib (n + 49)) % 7 + (Trib (n + 48) % 7)) % 7 := by
        rw [h_lhs]
        exact add_mod_gen (Trib (n + 50) + Trib (n + 49)) (Trib (n + 48)) 7
      have h_lhs_mod' : (Trib (n + 50) + Trib (n + 49)) % 7
          = ((Trib (n + 50) % 7) + (Trib (n + 49) % 7)) % 7 :=
        add_mod_gen (Trib (n + 50)) (Trib (n + 49)) 7
      have h_rhs_mod : Trib (n + 3) % 7
          = ((Trib (n + 2) + Trib (n + 1)) % 7 + (Trib n % 7)) % 7 := by
        rw [h_rhs]
        exact add_mod_gen (Trib (n + 2) + Trib (n + 1)) (Trib n) 7
      have h_rhs_mod' : (Trib (n + 2) + Trib (n + 1)) % 7
          = ((Trib (n + 2) % 7) + (Trib (n + 1) % 7)) % 7 :=
        add_mod_gen (Trib (n + 2)) (Trib (n + 1)) 7
      have h_swap : ((Trib (n + 50) % 7) + (Trib (n + 49) % 7)) % 7
                  = ((Trib (n + 2) % 7) + (Trib (n + 1) % 7)) % 7 := by
        rw [ih1', ih2']
      show Trib ((n + 3) + 48) % 7 = Trib (n + 3) % 7
      have h_indices : (n + 3) + 48 = n + 51 := by rfl
      rw [h_indices, h_lhs_mod, h_lhs_mod', h_swap, ← h_rhs_mod', ih0, ← h_rhs_mod]

/-! ## §7 Capstone (mod-{2, 3, 5, 7} closure) -/

/-- ★★★ **Tribonacci modular-fingerprint capstone (full tetrad)**.
    Four parametric Pisano closures across `{2, 3, 5, 7}`:
    π = 4, 13, 31, 48 respectively.  Period coincidences:
    π(5) = 31 with Narayana; π(7) = 48 with Padovan. -/
theorem capstone :
    (∀ n, Trib (n + 4) % 2 = Trib n % 2)
    ∧ (∀ n, Trib (n + 13) % 3 = Trib n % 3)
    ∧ (∀ n, Trib (n + 31) % 5 = Trib n % 5)
    ∧ (∀ n, Trib (n + 48) % 7 = Trib n % 7) :=
  ⟨Trib_mod_2_period_4, Trib_mod_3_period_13, Trib_mod_5_period_31,
   Trib_mod_7_period_48⟩

end E213.Lib.Math.Cohomology.Fractal.TribonacciModular
