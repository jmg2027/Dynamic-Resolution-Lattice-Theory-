import E213.Lib.Math.Cohomology.Fractal.Level
import E213.Meta.Tactic.NatHelper

/-!
# Fractal-level configuration count

`configCountD d n` is the count-Lens readout at fractal level `n`
with base `d` — the number of distinguishable configurations of a
level-`n` fractal complex with `d^n` vertices, each carrying `d`
states.

Combinatorial reading: `configCountD d n` is the number of
`n`-variable `d`-valued functions `[d]^n → [d]`.

The `d = 5` specialisation `configCount n := configCountD 5 n` is
the slice selected at the physics lens by
`Theory.Atomicity.Five.atomic_iff_five` and the three-pillar
forcing chain (PairForcing, C2a cohomology-loss, C2b adjoint-
product identity).  Other bases are mathematically well-defined
but have no physical reading.

Per CLAUDE.md "Universe-constant framing" failure mode:
numerical readouts are Lens outputs, parametric in both base and
level; the physics selection sits in `Theory.Atomicity`, not in
this file.

## Values (`d = 5` slice)

| n | numV n = 5^n | configCount n = 5^(5^n) |
|---|---|---|
| 0 | 1 | 5 |
| 1 | 5 | 3125 |
| 2 | 25 | 298023223876953125 (display-aliased `N_U`) |
| 3 | 125 | 5^125 (≈ 2.35 × 10^87) |
-/

namespace E213.Lib.Math.Cohomology.Fractal.ConfigCount

open E213.Lib.Math.Cohomology.Fractal.Level (numV)
open E213.Tactic.NatHelper (mul_assoc)

/-! ## Power helpers (213-native, kernel-pure)

`Nat.pow_mul` and `Nat.pow_succ` from Lean core bring `propext`
through `rw`-style rewrites.  Reproduced here via structural
recursion on the exponent, using only `Eq.subst` (`▸`) and
`mul_assoc` from `NatHelper`. -/

/-- `a^(n + k) = a^n * a^k`.  Structural recursion on `k`. -/
theorem pow_add_pure : ∀ (a n k : Nat), a^(n + k) = a^n * a^k
  | _, _, 0     => (Nat.mul_one _).symm
  | a, n, k + 1 => by
      show a^(n + k) * a = a^n * (a^k * a)
      have ih : a^(n + k) = a^n * a^k := pow_add_pure a n k
      have h1 : a^(n + k) * a = a^n * a^k * a := ih ▸ rfl
      have h2 : a^n * a^k * a = a^n * (a^k * a) := mul_assoc _ _ _
      exact h1.trans h2

/-- `a^(m * k) = (a^m)^k`.  Structural recursion on `k`. -/
theorem pow_mul_pure : ∀ (a m k : Nat), a^(m * k) = (a^m)^k
  | _, _, 0     => rfl
  | a, m, k + 1 => by
      show a^(m * k + m) = (a^m)^k * a^m
      have h_add : a^(m * k + m) = a^(m * k) * a^m := pow_add_pure a (m * k) m
      have ih : a^(m * k) = (a^m)^k := pow_mul_pure a m k
      exact h_add.trans (ih ▸ rfl)

/-- `1 ≤ a → 1 ≤ a^k`.  Structural recursion on `k`.
    Base step uses `1 * 1 = 1` definitionally; inductive step
    uses `Nat.mul_le_mul`. -/
private theorem one_le_pow_pure (a : Nat) (h : 1 ≤ a) : ∀ k, 1 ≤ a^k
  | 0     => Nat.le.refl
  | k + 1 => by
      show 1 ≤ a^k * a
      have ih : 1 ≤ a^k := one_le_pow_pure a h k
      exact Nat.mul_le_mul ih h

/-- `m ≤ m^d` for `m ≥ 1` and `d ≥ 1`.  Used to show that
    `level-up` (`configCountD_succ`) never decreases the count.
    Uses explicit `Eq.subst` motive to avoid `▸` motive inference
    picking the wrong occurrence pattern. -/
private theorem le_self_pow_pure : ∀ (m d : Nat), 1 ≤ m → 1 ≤ d → m ≤ m^d
  | _, 0,     _,  hd => absurd hd (Nat.not_succ_le_zero 0)
  | m, k + 1, hm, _  => by
      show m ≤ m^k * m
      have h_pow : 1 ≤ m^k := one_le_pow_pure m hm k
      have step : 1 * m ≤ m^k * m := Nat.mul_le_mul_right m h_pow
      -- Replace the `1 * m` on the LHS with `m` via explicit motive.
      exact @Eq.subst Nat (fun x => x ≤ m^k * m) (1 * m) m (Nat.one_mul m) step

/-- `a ≤ b → a^k ≤ b^k`.  Base monotonicity of `Nat.pow`, proved by
    structural recursion on `k` with `Nat.mul_le_mul`. -/
private theorem pow_le_pow_base : ∀ (a b k : Nat), a ≤ b → a^k ≤ b^k
  | _, _, 0,     _ => Nat.le.refl
  | a, b, k + 1, h => by
      show a^k * a ≤ b^k * b
      have ih : a^k ≤ b^k := pow_le_pow_base a b k h
      exact Nat.mul_le_mul ih h

/-- `a^k ≤ a^(k+1)` for `1 ≤ a`.  Single-step monotonicity in the
    exponent, used as the inductive step of `pow_le_pow_exp`. -/
private theorem pow_le_succ (a : Nat) (h : 1 ≤ a) (k : Nat) :
    a^k ≤ a^(k+1) := by
  show a^k ≤ a^k * a
  have hle : a^k * 1 ≤ a^k * a := Nat.mul_le_mul_left (a^k) h
  exact @Eq.subst Nat (fun x => x ≤ a^k * a) (a^k * 1) (a^k) (Nat.mul_one (a^k)) hle

/-- `m ≤ n → 1 ≤ a → a^m ≤ a^n`.  Exponent monotonicity, by
    induction on the `Nat.le` proof. -/
private theorem pow_le_pow_exp (a : Nat) (h : 1 ≤ a) {m : Nat} :
    ∀ {n : Nat}, m ≤ n → a^m ≤ a^n := by
  intro n hmn
  induction hmn with
  | refl       => exact Nat.le.refl
  | step _ ih  => exact Nat.le_trans ih (pow_le_succ a h _)

/-- Parametric count-Lens readout: configurations of a level-`n`
    fractal complex with `d^n` vertices, each carrying `d` states. -/
def configCountD (d n : Nat) : Nat := d ^ (d ^ n)

/-- Display alias: the `d = 5` slice, selected at the physics lens
    by `Theory.Atomicity.Five.atomic_iff_five`. -/
abbrev configCount (n : Nat) : Nat := configCountD 5 n

/-! ## Concrete values (decide-checked) -/

/-- `configCount 0 = 5^1 = 5`. -/
theorem configCount_zero : configCount 0 = 5 := by decide

/-- `configCount 1 = 5^5 = 3125`. -/
theorem configCount_one : configCount 1 = 3125 := by decide

/-- `configCount 2 = 5^25 = 298_023_223_876_953_125`.

    This is the value historically called `N_U`.  Demoted to one
    value of the `configCount` family per G120. -/
theorem configCount_two : configCount 2 = 298023223876953125 := by decide

/-- `configCount 2 = 5^25` (structural form). -/
theorem configCount_two_pow : configCount 2 = 5 ^ 25 := by decide

/-! ## Bridge to `numV` -/

/-- `configCount n = 5 ^ numV n`.  Unfolds the definition. -/
theorem configCount_eq_pow_numV (n : Nat) :
    configCount n = 5 ^ numV n := rfl

/-- `configCountD 5 n = configCount n`.  Bridges the parametric
    family to the `d = 5` display alias.  Free `rfl` because
    `configCount` is an `abbrev`. -/
theorem configCountD_at_5_eq (n : Nat) :
    configCountD 5 n = configCount n := rfl

/-! ## Structural identities (parametric in `d`) -/

/-- Base case: `configCountD d 0 = d` (since `d^0 = 1` and `d^1 = d`). -/
theorem configCountD_zero (d : Nat) : configCountD d 0 = d := by
  show d ^ (d ^ 0) = d
  rw [Nat.pow_zero, Nat.pow_one]

/-- `configCountD d 1 = d^d`. -/
theorem configCountD_one (d : Nat) : configCountD d 1 = d ^ d := by
  show d ^ (d ^ 1) = d ^ d
  rw [Nat.pow_one]

/-- Clean recursion — the canonical "level-up" operation:
    going from level `n` to level `n+1` raises the count to the
    `d`-th power.

    Proof: `d^(d^(n+1))` is definitionally `d^(d^n * d)` (via the
    `Nat.pow` definition), and `d^(d^n * d) = (d^(d^n))^d` by
    the 213-native `pow_mul_pure`. -/
theorem configCountD_succ (d n : Nat) :
    configCountD d (n + 1) = (configCountD d n) ^ d := by
  show d ^ (d ^ n * d) = (d ^ (d ^ n)) ^ d
  exact pow_mul_pure d (d ^ n) d

/-- Diagonal hit: `configCountD d d = d^(d^d)`.  At the diagonal
    `n = d`, the family lands on tetration depth 3 (`d↑↑3`). -/
theorem configCountD_diagonal (d : Nat) :
    configCountD d d = d ^ (d ^ d) := rfl

/-- Positivity: `1 ≤ d → 1 ≤ configCountD d n`.  Follows from
    `one_le_pow_pure` applied at exponent `d^n`. -/
theorem configCountD_pos (d n : Nat) (h : 1 ≤ d) :
    1 ≤ configCountD d n := by
  show 1 ≤ d ^ (d ^ n)
  exact one_le_pow_pure d h (d ^ n)

/-- Monotonicity in `n`: levelling up never decreases the count
    (provided the base satisfies `1 ≤ d`).  Follows from the
    clean recursion + `le_self_pow_pure`. -/
theorem configCountD_mono_n (d n : Nat) (h : 1 ≤ d) :
    configCountD d n ≤ configCountD d (n + 1) := by
  have hsucc : configCountD d (n + 1) = (configCountD d n) ^ d :=
    configCountD_succ d n
  have hpos : 1 ≤ configCountD d n := configCountD_pos d n h
  have hself : configCountD d n ≤ (configCountD d n) ^ d :=
    le_self_pow_pure (configCountD d n) d hpos h
  exact hsucc.symm ▸ hself

/-- Monotonicity in `d`: increasing the base (with both bases at
    least one) never decreases the count.  Two-step chain through
    `d^(e^n)`: first exponent monotonicity (`pow_le_pow_exp`), then
    base monotonicity (`pow_le_pow_base`). -/
theorem configCountD_mono_d (d e n : Nat) (hd : 1 ≤ d) (h : d ≤ e) :
    configCountD d n ≤ configCountD e n := by
  show d ^ (d ^ n) ≤ e ^ (e ^ n)
  -- Step 1: `d^n ≤ e^n` by base monotonicity.
  have h1 : d ^ n ≤ e ^ n := pow_le_pow_base d e n h
  -- Step 2: `d^(d^n) ≤ d^(e^n)` by exponent monotonicity (needs `1 ≤ d`).
  have h2 : d ^ (d ^ n) ≤ d ^ (e ^ n) := pow_le_pow_exp d hd h1
  -- Step 3: `d^(e^n) ≤ e^(e^n)` by base monotonicity again.
  have h3 : d ^ (e ^ n) ≤ e ^ (e ^ n) := pow_le_pow_base d e (e ^ n) h
  exact Nat.le_trans h2 h3

/-! ## Concrete per-`d` values at `n = 2` (decide-checked) -/

/-- `configCountD 2 2 = 2^4 = 16`. -/
theorem configCountD_2_2 : configCountD 2 2 = 16 := by decide

/-- `configCountD 3 2 = 3^9 = 19683`. -/
theorem configCountD_3_2 : configCountD 3 2 = 19683 := by decide

/-- `configCountD 5 2 = 5^25 = 298_023_223_876_953_125`
    (the value display-aliased `N_U`). -/
theorem configCountD_5_2 : configCountD 5 2 = 298023223876953125 := by decide

/-- `configCountD 7 2 = 7^49` (structural — the decimal expansion
    is around 2.56 × 10^41).  Stated structurally to keep the
    proof a one-line `rfl`. -/
theorem configCountD_7_2 : configCountD 7 2 = 7 ^ 49 := rfl

end E213.Lib.Math.Cohomology.Fractal.ConfigCount
