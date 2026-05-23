import E213.Lib.Math.Cohomology.Fractal.NarayanaCutoff
import E213.Meta.Nat.AddMod213

/-!
# Narayana-cow-sequence modular fingerprint

Companion to `NarayanaCutoff.lean` — Pisano-period analogue for
the Narayana cow sequence mod 2.

The 3-step recurrence `N_{n+3} = N_{n+2} + N_n` (one-shift cousin
of Padovan) mod 2 has period 7 — same period as Padovan, despite
the different recurrence structure.  Pisano-analogue twins.

## Periods at small primes

| p | π_N(p) | first cycle (`N_0..N_{π−1} mod p`) |
|---|--------|------------------------------------|
| 2 | 7      | `1, 1, 1, 0, 1, 0, 0` ★ parametric |

## Why period 7 mod 2 is structural

Among `2³ = 8` mod-2 triples, the orbit starting at
`(N_0, N_1, N_2) = (1, 1, 1)` mod 2 cycles through 7 distinct
triples and returns — the absorbing `(0, 0, 0)` triple is not
on the orbit.  Hence π_N(2) = 7.

Padovan and Narayana cow share `π(2) = 7` despite having
different mod-2 cycles:

  · Padovan mod 2: `1, 1, 1, 0, 0, 1, 0` (cycle through 7 triples)
  · Narayana mod 2: `1, 1, 1, 0, 1, 0, 0` (different cycle, same
    length)

The shared period is a structural twin — both 3-step recurrences
with `(P_n + 2_terms)` or `(N_n + 2_terms)` parity-coupling
produce a 7-orbit on the 7 non-absorbing mod-2 triples.
-/

namespace E213.Lib.Math.Cohomology.Fractal.NarayanaModular

open E213.Lib.Math.Cohomology.Fractal.NarayanaCutoff (Nara)
open E213.Meta.Nat.AddMod213

/-! ## §1 Mod-2 small table (decide-checked) -/

theorem Nara_0_mod_2  : Nara 0  % 2 = 1 := by decide
theorem Nara_1_mod_2  : Nara 1  % 2 = 1 := by decide
theorem Nara_2_mod_2  : Nara 2  % 2 = 1 := by decide
theorem Nara_3_mod_2  : Nara 3  % 2 = 0 := by decide
theorem Nara_4_mod_2  : Nara 4  % 2 = 1 := by decide
theorem Nara_5_mod_2  : Nara 5  % 2 = 0 := by decide
theorem Nara_6_mod_2  : Nara 6  % 2 = 0 := by decide
theorem Nara_7_mod_2  : Nara 7  % 2 = 1 := by decide
theorem Nara_8_mod_2  : Nara 8  % 2 = 1 := by decide
theorem Nara_9_mod_2  : Nara 9  % 2 = 1 := by decide

/-! ## §2 Period 7 mod 2 — parametric

3-step strong induction on `n`.  Base cases at `n ∈ {0, 1, 2}`
verified by `decide`; inductive step at `n + 3` uses the
recurrence `Nara ((n+3) + 7) = Nara (n+10)
= Nara (n+9) + Nara (n+7)` (one-index-shift recurrence) combined
with `Nara (n+3) = Nara (n+2) + Nara n`. -/

/-- ★ **Period 7 mod 2 for Narayana**:
    `Nara (n + 7) % 2 = Nara n % 2` for every `n : Nat`.

    Pisano-period twin to Padovan: both have π(2) = 7 despite
    different mod-2 cycles. -/
theorem Nara_mod_2_period_7 : ∀ n, Nara (n + 7) % 2 = Nara n % 2
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      -- Narayana recurrence at index n+7: Nara (n+10) = Nara (n+9) + Nara (n+7).
      have h_lhs : Nara (n + 10) = Nara (n + 9) + Nara (n + 7) := by
        show Nara ((n + 7) + 3) = Nara (n + 9) + Nara (n + 7)
        rfl
      -- Narayana recurrence at index n: Nara (n+3) = Nara (n+2) + Nara n.
      have h_rhs : Nara (n + 3) = Nara (n + 2) + Nara n := rfl
      -- IHs at n and n+2.  Note: due to the one-shift recurrence
      -- we need IH at n+2 (giving Nara (n+9)) and IH at n (giving
      -- Nara (n+7)).
      have ih0 : Nara (n + 7) % 2 = Nara n % 2 :=
        Nara_mod_2_period_7 n
      have ih2 : Nara ((n + 2) + 7) % 2 = Nara (n + 2) % 2 :=
        Nara_mod_2_period_7 (n + 2)
      have ih2' : Nara (n + 9) % 2 = Nara (n + 2) % 2 := ih2
      -- Reduce the LHS sum mod 2 via add_mod_gen.
      have h_lhs_mod : Nara (n + 10) % 2
          = ((Nara (n + 9) % 2) + (Nara (n + 7) % 2)) % 2 := by
        rw [h_lhs]; exact add_mod_gen (Nara (n + 9)) (Nara (n + 7)) 2
      have h_rhs_mod : Nara (n + 3) % 2
          = ((Nara (n + 2) % 2) + (Nara n % 2)) % 2 := by
        rw [h_rhs]; exact add_mod_gen (Nara (n + 2)) (Nara n) 2
      -- Substitute IHs.
      have h_swap : ((Nara (n + 9) % 2) + (Nara (n + 7) % 2)) % 2
                  = ((Nara (n + 2) % 2) + (Nara n % 2)) % 2 := by
        rw [ih0, ih2']
      -- Chain.
      show Nara ((n + 3) + 7) % 2 = Nara (n + 3) % 2
      have h_indices : (n + 3) + 7 = n + 10 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §3 Mod-3 small table (decide-checked) -/

theorem Nara_0_mod_3  : Nara 0  % 3 = 1 := by decide
theorem Nara_1_mod_3  : Nara 1  % 3 = 1 := by decide
theorem Nara_2_mod_3  : Nara 2  % 3 = 1 := by decide
theorem Nara_8_mod_3  : Nara 8  % 3 = 1 := by decide
theorem Nara_9_mod_3  : Nara 9  % 3 = 1 := by decide
theorem Nara_10_mod_3 : Nara 10 % 3 = 1 := by decide

/-! ## §4 Period 8 mod 3 — parametric

3-step strong induction on `n`.  Base cases at `n ∈ {0, 1, 2}`
verified by `decide`; inductive step at `n + 3` uses the
Narayana recurrence `Nara ((n+8)+3) = Nara (n+11)
= Nara (n+10) + Nara (n+8)` (one-shift: no middle term)
combined with `Nara (n + 3) = Nara (n + 2) + Nara n`. -/

/-- ★ **Period 8 mod 3 for Narayana**:
    `Nara (n + 8) % 3 = Nara n % 3` for every `n : Nat`.

    Mod-3 period for Narayana is 8 (vs. Padovan's 13) — the
    one-shift recurrence on different-modulus orbits diverges
    even when the mod-2 periods match. -/
theorem Nara_mod_3_period_8 : ∀ n, Nara (n + 8) % 3 = Nara n % 3
  | 0     => by decide
  | 1     => by decide
  | 2     => by decide
  | n + 3 => by
      have h_lhs : Nara (n + 11) = Nara (n + 10) + Nara (n + 8) := by
        show Nara ((n + 8) + 3) = Nara (n + 10) + Nara (n + 8)
        rfl
      have h_rhs : Nara (n + 3) = Nara (n + 2) + Nara n := rfl
      have ih0 : Nara (n + 8) % 3 = Nara n % 3 := Nara_mod_3_period_8 n
      have ih2 : Nara ((n + 2) + 8) % 3 = Nara (n + 2) % 3 :=
        Nara_mod_3_period_8 (n + 2)
      have ih2' : Nara (n + 10) % 3 = Nara (n + 2) % 3 := ih2
      have h_lhs_mod : Nara (n + 11) % 3
          = ((Nara (n + 10) % 3) + (Nara (n + 8) % 3)) % 3 := by
        rw [h_lhs]; exact add_mod_gen (Nara (n + 10)) (Nara (n + 8)) 3
      have h_rhs_mod : Nara (n + 3) % 3
          = ((Nara (n + 2) % 3) + (Nara n % 3)) % 3 := by
        rw [h_rhs]; exact add_mod_gen (Nara (n + 2)) (Nara n) 3
      have h_swap : ((Nara (n + 10) % 3) + (Nara (n + 8) % 3)) % 3
                  = ((Nara (n + 2) % 3) + (Nara n % 3)) % 3 := by
        rw [ih0, ih2']
      show Nara ((n + 3) + 8) % 3 = Nara (n + 3) % 3
      have h_indices : (n + 3) + 8 = n + 11 := by rfl
      rw [h_indices, h_lhs_mod, h_swap, ← h_rhs_mod]

/-! ## §5 Capstone -/

/-- ★★★ **Narayana modular-fingerprint capstone**.  Two
    parametric Pisano closures: period 7 mod 2 (twin to Padovan)
    + period 8 mod 3 (one-shift recurrence diverges from
    Padovan's mod-3 period 13). -/
theorem capstone :
    -- Parametric period 7 mod 2 (Pisano twin to Padovan)
    (∀ n, Nara (n + 7) % 2 = Nara n % 2)
    -- Parametric period 8 mod 3 (diverges from Padovan's 13)
    ∧ (∀ n, Nara (n + 8) % 3 = Nara n % 3) :=
  ⟨Nara_mod_2_period_7, Nara_mod_3_period_8⟩

end E213.Lib.Math.Cohomology.Fractal.NarayanaModular
