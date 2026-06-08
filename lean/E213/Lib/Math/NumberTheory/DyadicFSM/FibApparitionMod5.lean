import E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod
import E213.Lib.Math.NumberTheory.DyadicFSM.LucasFSMmod5
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
import E213.Meta.Nat.AddMod213

/-!
# Fibonacci rank of apparition at the ramified prime 5

`5` is the discriminant of `x² − x − 1`, so it is the unique **ramified**
prime of the golden modulus `ℚ(√5) = ℚ(φ)` (`x² − x − 1 ≡ (x − 3)² mod 5`,
double root `α ≡ β ≡ 3`).  At a double root the two Binet branches collapse:

  * `Lⁿ = αⁿ + βⁿ` stays **regular** — `L_n ≡ 2·3ⁿ`, never `0 mod 5`.
  * `Fⁿ = (αⁿ − βⁿ)/(α − β)` is **singular** — `F_n ≡ n·3ⁿ⁻¹`, vanishing
    exactly when `5 ∣ n`.

The `LucasFSMmod5` docstring states this divergence verbally (regular vs
singular at ramification).  This file proves it ∅-axiom, reading the two
FSMs' periodic zero-sets:

  * **Fibonacci** (`fibFSMmod5`, period `20 = 4p`): `5 ∣ F_n ⟺ 5 ∣ n`.
    The **rank of apparition** is `α(5) = 5 = p` itself — the ramified-prime
    signature (generic primes have `α(p) ∣ p ± 1`; the ramified prime alone
    has `α(p) = p`).  And `F_5 = 5 = p`: the first Fibonacci `5` divides is
    `5`.
  * **Lucas** (`lucasFSMmod5`, period `4 = p − 1`): `L_n` is *never* `0 mod
    5` — no rank of apparition, the regular branch.

This is the arithmetic-first 5-adic handle of `research-notes/frontiers/
G124_padic_drlt_5adic.md` §"only 213-native form a future H can take": a
non-trivial 5-adic arithmetic invariant of an object the corpus already
builds (the golden / Cassini recurrence).  It ties the resolution prime `5`
(`configCount 2 = 5²⁵`) to the *ramified* prime of the DRLT golden modulus
(`R_u = 1/φ²`) through one structural fact — the singular/regular split of
the Binet branches at the double root.

The full 5-adic valuation lift `ν₅(F_n) = ν₅(n)` (lifting-the-exponent) is
the next rung; this file closes the `n = 1` rung (the zero-set / rank).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FibApparitionMod5

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod5 (fibFSMmod5 fibFSMmod5_run_period_20)
open E213.Lib.Math.NumberTheory.DyadicFSM.LucasFSMmod5 (lucasFSMmod5 lucasFSMmod5_run_period_4)

/-! ## `run` reduction modulo the period (generic helper) -/

/-- `run` has every multiple of its period as a period (Fin×Fin valued —
    the `bits_period_mul_of_period` analog for the raw run). -/
theorem run_period_mul {p : Nat} (m : ArithFSM2 p) {T : Nat}
    (h : ∀ k, m.run (k + T) = m.run k) :
    ∀ n k, m.run (k + n * T) = m.run k := by
  intro n
  induction n with
  | zero => intro k; rw [Nat.zero_mul, Nat.add_zero]
  | succ j ih =>
      intro k
      have hreshape : k + (j + 1) * T = (k + j * T) + T := by
        rw [Nat.succ_mul, ← Nat.add_assoc]
      rw [hreshape, h, ih]

/-- Reduce a `run` index to its residue modulo the period `T`. -/
theorem run_mod {p : Nat} (m : ArithFSM2 p) {T : Nat}
    (h : ∀ k, m.run (k + T) = m.run k) (n : Nat) :
    m.run n = m.run (n % T) := by
  have e : n % T + (n / T) * T = n := by
    rw [Nat.mul_comm (n / T) T, Nat.add_comm]
    exact E213.Meta.Nat.AddMod213.div_add_mod n T
  calc m.run n = m.run (n % T + (n / T) * T) := by rw [e]
    _ = m.run (n % T) := run_period_mul m h (n / T) (n % T)

/-! ## Fibonacci mod 5 — the singular branch -/

/-- `F_n mod 5`, the first state component of the Fibonacci FSM
    (`init = (F₀, F₁) = (0, 1)`, `step (a, b) = (b, a + b)`). -/
def fibMod5 (n : Nat) : Nat := (fibFSMmod5.run n).1.val

theorem fibMod5_mod20 (n : Nat) : fibMod5 n = fibMod5 (n % 20) := by
  unfold fibMod5
  rw [run_mod fibFSMmod5 fibFSMmod5_run_period_20 n]

/-- Over one period, `5 ∣ F_r ⟺ 5 ∣ r` (decidable finite check). -/
theorem fibMod5_zero_residue :
    ∀ r, r < 20 → (fibMod5 r = 0 ↔ r % 5 = 0) := by decide

/-- **Rank of apparition of `5`.**  `5 ∣ F_n ⟺ 5 ∣ n` — equivalently the
    zero-set of Fibonacci mod 5 is exactly `5·ℕ`. -/
theorem fibMod5_zero_iff (n : Nat) : fibMod5 n = 0 ↔ n % 5 = 0 := by
  rw [fibMod5_mod20 n,
      show n % 5 = (n % 20) % 5 from
        (E213.Meta.Nat.AddMod213.mod_mod_of_dvd n ⟨4, rfl⟩).symm]
  exact fibMod5_zero_residue (n % 20) (Nat.mod_lt n (by decide))

/-- `5 ∣ F_n ⟺ 5 ∣ n`, stated with divisibility. -/
theorem five_dvd_fib_iff (n : Nat) : fibMod5 n = 0 ↔ 5 ∣ n :=
  (fibMod5_zero_iff n).trans
    ⟨E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero,
     fun h => by
       rcases h with ⟨q, hq⟩; rw [hq]
       exact E213.Tactic.NatHelper.mul_mod_right 5 q⟩

/-- **`α(5) = 5` is tight.**  `5 ∣ F₅` and no smaller positive index
    qualifies — the rank of apparition equals the prime itself, the
    ramified signature.  (`F₅ = 5 = p`: the first Fibonacci divisible by
    `5` is `5`.) -/
theorem rank_apparition_five :
    fibMod5 5 = 0 ∧ ∀ m, m < 5 → 0 < m → fibMod5 m ≠ 0 := by
  refine ⟨by decide, ?_⟩
  decide

/-! ## Lucas mod 5 — the regular branch -/

/-- `L_n mod 5`, the first state component of the Lucas FSM
    (`init = (L₀, L₁) = (2, 1)`). -/
def lucasMod5 (n : Nat) : Nat := (lucasFSMmod5.run n).1.val

theorem lucasMod5_mod4 (n : Nat) : lucasMod5 n = lucasMod5 (n % 4) := by
  unfold lucasMod5
  rw [run_mod lucasFSMmod5 lucasFSMmod5_run_period_4 n]

/-- Over one period the Lucas residue is never `0` (decidable check;
    values cycle `2, 1, 3, 4`). -/
theorem lucasMod5_residue_ne_zero : ∀ r, r < 4 → lucasMod5 r ≠ 0 := by decide

/-- **Lucas has no rank of apparition mod 5.**  `5 ∤ L_n` for every `n` —
    the regular Binet branch at the ramified double root, the structural
    counterpart of Fibonacci's `5·ℕ` zero-set. -/
theorem lucasMod5_never_zero (n : Nat) : lucasMod5 n ≠ 0 := by
  rw [lucasMod5_mod4 n]
  exact lucasMod5_residue_ne_zero (n % 4) (Nat.mod_lt n (by decide))

/-! ## The `ν₅ ≥ 2` rung — Fibonacci mod 25

The next valuation rung toward `ν₅(F_n) = ν₅(n)`: the zero-set of
Fibonacci mod `25 = 5²`.  The Pisano period of `25` is `100 = 4·5²`, and
the zeros sit exactly at the multiples of `25` — i.e. `25 ∣ F_n ⟺ 25 ∣
n`, the `ν₅(·) ≥ 2` reading.  Proved the same way (period reduction +
finite decide), one prime power up.  (The full all-powers law
`ν₅(F_n) = ν₅(n)` is the open lifting-the-exponent rung — see
`research-notes/frontiers/G124_padic_drlt_5adic.md`.) -/

/-- Fibonacci-style FSM mod 25 (`init = (F₀, F₁) = (0, 1)`). -/
def fibFSMmod25 : ArithFSM2 25 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 25, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Fibonacci mod-25 run cycles with the Pisano period `100 = 4·5²`. -/
theorem fibFSMmod25_run_period_100 :
    ∀ k, fibFSMmod25.run (k + 100) = fibFSMmod25.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

/-- `F_n mod 25`. -/
def fibMod25 (n : Nat) : Nat := (fibFSMmod25.run n).1.val

theorem fibMod25_mod100 (n : Nat) : fibMod25 n = fibMod25 (n % 100) := by
  unfold fibMod25
  rw [run_mod fibFSMmod25 fibFSMmod25_run_period_100 n]

/-- Over one period, `25 ∣ F_r ⟺ 25 ∣ r` (decidable finite check;
    zeros at `r ∈ {0, 25, 50, 75}`). -/
theorem fibMod25_zero_residue :
    ∀ r, r < 100 → (fibMod25 r = 0 ↔ r % 25 = 0) := by decide

/-- **The `ν₅ ≥ 2` rung.**  `25 ∣ F_n ⟺ 25 ∣ n` — the zero-set of
    Fibonacci mod `25` is exactly `25·ℕ`. -/
theorem fibMod25_zero_iff (n : Nat) : fibMod25 n = 0 ↔ n % 25 = 0 := by
  rw [fibMod25_mod100 n,
      show n % 25 = (n % 100) % 25 from
        (E213.Meta.Nat.AddMod213.mod_mod_of_dvd n ⟨4, rfl⟩).symm]
  exact fibMod25_zero_residue (n % 100) (Nat.mod_lt n (by decide))

/-- `25 ∣ F_n ⟺ 25 ∣ n`, stated with divisibility. -/
theorem twentyfive_dvd_fib_iff (n : Nat) : fibMod25 n = 0 ↔ 25 ∣ n :=
  (fibMod25_zero_iff n).trans
    ⟨E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero,
     fun h => by
       rcases h with ⟨q, hq⟩; rw [hq]
       exact E213.Tactic.NatHelper.mul_mod_right 25 q⟩

/-! ## The divergence, packaged -/

/-- **Singular vs regular at the ramified prime `5`.**  The same recurrence
    `s_{n+1} = s_n + s_{n-1}` mod 5, two initial conditions: Fibonacci
    vanishes exactly on `5·ℕ` (rank of apparition `5`), Lucas never
    vanishes.  This is the FSM-level reading of the Binet-branch collapse
    `F_n ≡ n·3ⁿ⁻¹`, `L_n ≡ 2·3ⁿ` at the double root `α ≡ β ≡ 3 mod 5`. -/
theorem fib_lucas_apparition_divergence :
    (∀ n, fibMod5 n = 0 ↔ 5 ∣ n) ∧ (∀ n, lucasMod5 n ≠ 0) :=
  ⟨five_dvd_fib_iff, lucasMod5_never_zero⟩

end E213.Lib.Math.NumberTheory.DyadicFSM.FibApparitionMod5
