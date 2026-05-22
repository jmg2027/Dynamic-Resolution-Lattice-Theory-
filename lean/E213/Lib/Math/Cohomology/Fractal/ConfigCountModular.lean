import E213.Lib.Math.Cohomology.Fractal.ConfigCount

/-!
# `configCountD` modular reductions

For prime `p` coprime to base `d`, the sequence `n ↦ configCountD d n % p`
is eventually periodic with period dividing the multiplicative
order of `d` modulo `(p − 1)`.  The general parametric statement
lives downstream of `Lib/Math/ModArith/UniversalFLT`; here we
record concrete `decide`-checked instances at the physics-selected
base `d = 5` and a few small primes.

## Catalogue (at `d = 5`)

  · `configCountD 5 n % 2 = 1`   for all `n` (5 odd ⇒ 5^k odd)
  · `configCountD 5 n % 3 = 2`   for all `n` (5 ≡ 2 mod 3, 5^n odd,
                                  so 5^(5^n) ≡ 2^odd ≡ 2 mod 3)
  · `configCountD 5 n % 7`       period 2 in `n` from `n = 1`:
                                  5, 3, 5, 3, …
  · `configCountD 5 n % 11`      eventually periodic
  · `configCountD 5 n % 13`      period 2 in `n` from `n = 1`

The decimal-literal tables below are `decide`-checked; the
parametric eventual-periodicity statement is logged as an open
target (consumes `UniversalFLT.flt_main` + an explicit `ord`
enumeration).
-/

namespace E213.Lib.Math.Cohomology.Fractal.ConfigCountModular

open E213.Lib.Math.Cohomology.Fractal.ConfigCount (configCountD)

/-! ## `d = 5`, `p = 2` — constant 1 -/

theorem configCountD_5_0_mod_2 : configCountD 5 0 % 2 = 1 := by decide
theorem configCountD_5_1_mod_2 : configCountD 5 1 % 2 = 1 := by decide
theorem configCountD_5_2_mod_2 : configCountD 5 2 % 2 = 1 := by decide

/-! ## `d = 5`, `p = 3` — constant 2 -/

theorem configCountD_5_0_mod_3 : configCountD 5 0 % 3 = 2 := by decide
theorem configCountD_5_1_mod_3 : configCountD 5 1 % 3 = 2 := by decide
theorem configCountD_5_2_mod_3 : configCountD 5 2 % 3 = 2 := by decide

/-! ## `d = 5`, `p = 7` — period 2 (5, 3, 5, …) from `n = 1` -/

theorem configCountD_5_0_mod_7 : configCountD 5 0 % 7 = 5 := by decide
theorem configCountD_5_1_mod_7 : configCountD 5 1 % 7 = 3 := by decide
theorem configCountD_5_2_mod_7 : configCountD 5 2 % 7 = 5 := by decide

/-! ## `d = 5`, `p = 11`

`5 mod 10 = 5`; `gcd(5, 10) = 5 > 1`, so the multiplicative
order argument bottoms out — the modular sequence is eventually
constant after `n ≥ 1`. -/

theorem configCountD_5_0_mod_11 : configCountD 5 0 % 11 = 5 := by decide
theorem configCountD_5_1_mod_11 : configCountD 5 1 % 11 = 1 := by decide
theorem configCountD_5_2_mod_11 : configCountD 5 2 % 11 = 1 := by decide

/-! ## `d = 5`, `p = 13` — period 2 from `n = 1` -/

theorem configCountD_5_0_mod_13 : configCountD 5 0 % 13 = 5 := by decide
theorem configCountD_5_1_mod_13 : configCountD 5 1 % 13 = 5 := by decide
theorem configCountD_5_2_mod_13 : configCountD 5 2 % 13 = 5 := by decide

/-! ## Cross-base level-2 sample at small primes

The level-2 readout per base, modulo a fixed small prime, brings
out the structural per-base differences. -/

theorem configCountD_2_2_mod_7 : configCountD 2 2 % 7 = 2 := by decide   -- 16 mod 7
theorem configCountD_3_2_mod_7 : configCountD 3 2 % 7 = 6 := by decide   -- 3^9 mod 7
theorem configCountD_5_2_mod_7' : configCountD 5 2 % 7 = 5 := by decide

/-! ## Capstone — modular table at the physics-selected base

Bundles the small-prime modular readouts at the physics base
`d = 5` and level `n = 2` (`= N_U`).  Records that the `N_U` value
agrees with the per-prime FLT-reduced computation. -/

theorem configCountD_5_2_mod_table :
    configCountD 5 2 % 2 = 1
    ∧ configCountD 5 2 % 3 = 2
    ∧ configCountD 5 2 % 5 = 0
    ∧ configCountD 5 2 % 7 = 5
    ∧ configCountD 5 2 % 11 = 1
    ∧ configCountD 5 2 % 13 = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Fractal.ConfigCountModular
