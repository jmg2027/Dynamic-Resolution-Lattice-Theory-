/-!
# Mod213 — cohomological trajectory primitives (∅-axiom)

213-native modular arithmetic via *step-N structural recursion*,
not Lean's well-founded `% n` (which forces propext through
`Nat.add_mod_right` etc.).

Rationale (`research-notes/G2_trajectory_principle.md`,
`G3_raw_as_universal_trajectory.md`):

  - Lean's `Nat.mod` = well-founded recursion → reduction lemmas
    bring `propext`.
  - 213's view: mod = "how much an N-cycle trajectory has not yet
    closed" — a path, not a quotient endpoint.
  - Defining mod by step-N recursion makes every reduction lemma
    a structural `rfl`.  ∅-axiom by construction.

Atomic alphabet {2, 3} (from `Firmware/Atomicity/NonDecomposable`):
every `n ≥ 2 = 2a + 3b` (Frobenius), so all modular trajectories
cascade from `parity` (mod 2) and `mod3` (mod 3) — exactly what
this module provides.

`mod6` + the CRT pairing (`mod6_parity`, `mod6_mod3`) realise the
ℤ/6 ≅ ℤ/2 × ℤ/3 walk — the Eisenstein-6th-roots-of-unity phase
trajectory underlying the K_{3,2}^{(2)} signature graph.
-/

namespace E213.Tactic.Mod213

/-! ### mod 2 — parity (smallest cohomological-trajectory primitive) -/

/-- 213-native parity.  Step-2 recursion = "uncompleted half-cycle". -/
def parity : Nat → Bool
  | 0     => false
  | 1     => true
  | n + 2 => parity n

@[simp] theorem parity_step (n : Nat) : parity (n + 2) = parity n := rfl
@[simp] theorem parity_zero : parity 0 = false := rfl
@[simp] theorem parity_one : parity 1 = true := rfl

theorem parity_succ : ∀ n, parity (n + 1) = !parity n
  | 0     => rfl
  | 1     => rfl
  | n + 2 => parity_succ n

theorem parity_double : ∀ n, parity (2 * n) = false
  | 0     => rfl
  | n + 1 => parity_double n

theorem parity_double_succ : ∀ n, parity (2 * n + 1) = true
  | 0     => rfl
  | n + 1 => parity_double_succ n

end E213.Tactic.Mod213

namespace E213.Tactic.Mod213

/-! ### mod 3 — second atomic primitive (NS = 3) -/

/-- 213-native mod 3.  Step-3 recursion = "walk on 3-cycle". -/
def mod3 : Nat → Nat
  | 0     => 0
  | 1     => 1
  | 2     => 2
  | n + 3 => mod3 n

@[simp] theorem mod3_step (n : Nat) : mod3 (n + 3) = mod3 n := rfl
@[simp] theorem mod3_zero : mod3 0 = 0 := rfl
@[simp] theorem mod3_one  : mod3 1 = 1 := rfl
@[simp] theorem mod3_two  : mod3 2 = 2 := rfl

/-- Bound: `mod3 n < 3` — ∅-axiom via `Nat.le.step` chain. -/
theorem mod3_lt_three : ∀ n, mod3 n < 3
  | 0     => Nat.le.step (Nat.le.step Nat.le.refl)
  | 1     => Nat.le.step Nat.le.refl
  | 2     => Nat.le.refl
  | n + 3 => mod3_lt_three n

/-- mod3 cycles `0 → 1 → 2 → 0 → …`. -/
theorem mod3_succ : ∀ n, mod3 (n + 1) = (mod3 n + 1) % 3
  | 0     => rfl
  | 1     => rfl
  | 2     => rfl
  | n + 3 => mod3_succ n

end E213.Tactic.Mod213

namespace E213.Tactic.Mod213

/-! ### mod 6 — explicit CRT pairing ℤ/6 ≅ ℤ/2 × ℤ/3

This is the Eisenstein-6th-roots-of-unity walk underlying the
K_{3,2}^{(2)} signature graph (NS=3, NT=2, d=5; phase = mod 6).
-/

/-- 213-native mod 6 via step-6 recursion. -/
def mod6 : Nat → Nat
  | 0     => 0
  | 1     => 1
  | 2     => 2
  | 3     => 3
  | 4     => 4
  | 5     => 5
  | n + 6 => mod6 n

@[simp] theorem mod6_step (n : Nat) : mod6 (n + 6) = mod6 n := rfl

theorem mod6_lt_six : ∀ n, mod6 n < 6
  | 0 => Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step
           (Nat.le.step Nat.le.refl))))
  | 1 => Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl)))
  | 2 => Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl))
  | 3 => Nat.le.step (Nat.le.step Nat.le.refl)
  | 4 => Nat.le.step Nat.le.refl
  | 5 => Nat.le.refl
  | n + 6 => mod6_lt_six n

/-- CRT pairing (half 1): `parity (mod6 n) = parity n`. -/
theorem mod6_parity : ∀ n, parity (mod6 n) = parity n
  | 0 => rfl | 1 => rfl | 2 => rfl
  | 3 => rfl | 4 => rfl | 5 => rfl
  | n + 6 => mod6_parity n

/-- CRT pairing (half 2): `mod3 (mod6 n) = mod3 n`. -/
theorem mod6_mod3 : ∀ n, mod3 (mod6 n) = mod3 n
  | 0 => rfl | 1 => rfl | 2 => rfl
  | 3 => rfl | 4 => rfl | 5 => rfl
  | n + 6 => mod6_mod3 n

end E213.Tactic.Mod213
