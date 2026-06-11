import E213.Lib.Math.Foundations.UniverseChain.AtomicityCensusBridge

/-!
# Quadratic normal form + mod-5 dynamics of the Raw census (∅-axiom)

The census recursion `rawCount (n+1) = 2 + choose2 (rawCount n)` is a
quadratic map in disguise.  Subtraction-free normal form:

  `2·T(n+1) + T(n) = T(n)² + 4`

(equivalently `8·T(n+1) = (2·T(n) − 1)² + 15` over ℤ — the map is
conjugate to `w ↦ w² + 11/16`).

Mod 5 the orbit is **purely periodic with period 3**, cycling through
`(2, 3, 0)` — the depth-0/1/2 populations read mod 5.  This is an
instance of a *generic self-restart*: for any tower
`f(x) = 2 + q(x)` with `q(0) = 0`, the orbit mod its own depth-2
value `f(f(2))` restarts at `2` every three steps (each clause
variant does the same mod its own depth-2 value: 17, 38, 14).  The
only 213-specific content is that the depth-2 value here *is* 5 —
already the census theorem `rawCount 2 = 5`.  No resonance is
claimed; no level is privileged.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawCountQuadratic

open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence
  (choose2 rawCount rawCount_succ)
open E213.Lib.Math.Foundations.UniverseChain.AtomicityCensusBridge
  (choose2_succ)
open E213.Tactic.NatHelper

-- ═══ choose2 algebra ═══

/-- Vandermonde for the pair count:
    `C(a+b, 2) = C(a,2) + C(b,2) + a·b`. -/
theorem choose2_add : ∀ (a b : Nat),
    choose2 (a + b) = choose2 a + choose2 b + a * b
  | _, 0 => rfl
  | a, b + 1 => by
    have ih := choose2_add a b
    calc choose2 (a + (b + 1))
        = choose2 (a + b) + (a + b) := choose2_succ (a + b)
      _ = choose2 a + choose2 b + a * b + (a + b) := by rw [ih]
      _ = choose2 a + (choose2 b + b) + (a * b + a) := by
            rw [Nat.add_assoc (choose2 a + choose2 b) (a * b) (a + b),
                ← Nat.add_assoc (a * b) a b,
                Nat.add_comm (a * b + a) b,
                ← Nat.add_assoc (choose2 a + choose2 b) b (a * b + a),
                Nat.add_assoc (choose2 a) (choose2 b) b]
      _ = choose2 a + choose2 (b + 1) + a * (b + 1) := by
            rw [← choose2_succ b, ← Nat.mul_succ a b]

private theorem dshuffle (A n : Nat) :
    A + (n + n) + (n + 1) = (A + n) + (n + n + 1) := by
  rw [← Nat.add_assoc (A + (n + n)) n 1, ← Nat.add_assoc A n n,
      ← Nat.add_assoc (A + n) (n + n) 1, ← Nat.add_assoc (A + n) n n]

private theorem sqshuffle (n : Nat) :
    n * n + (n + n + 1) = (n + 1) * (n + 1) := by
  rw [Nat.succ_mul n (n + 1), Nat.mul_succ n n,
      ← Nat.add_assoc (n * n) (n + n) 1, ← Nat.add_assoc (n * n) n n,
      Nat.add_assoc (n * n + n) n 1]

/-- Subtraction-free doubling: `2·C(n,2) + n = n²`. -/
theorem choose2_double : ∀ n : Nat, 2 * choose2 n + n = n * n
  | 0 => rfl
  | n + 1 => by
    have ih := choose2_double n
    calc 2 * choose2 (n + 1) + (n + 1)
        = 2 * (choose2 n + n) + (n + 1) := by rw [choose2_succ n]
      _ = 2 * choose2 n + (n + n) + (n + 1) := by
            rw [Nat.mul_add 2 (choose2 n) n, two_mul n]
      _ = (2 * choose2 n + n) + (n + n + 1) := dshuffle (2 * choose2 n) n
      _ = n * n + (n + n + 1) := by rw [ih]
      _ = (n + 1) * (n + 1) := sqshuffle n

/-- ★ **Quadratic normal form** (subtraction-free):
    `2·T(n+1) + T(n) = T(n)² + 4`.  Over ℤ this is
    `8·T(n+1) = (2·T(n) − 1)² + 15` — the census recursion is a
    conjugated pure quadratic map. -/
theorem rawCount_normal_form (n : Nat) :
    2 * rawCount (n + 1) + rawCount n
      = rawCount n * rawCount n + 4 := by
  rw [rawCount_succ, Nat.mul_add,
      Nat.add_assoc (2 * 2) (2 * choose2 (rawCount n)) (rawCount n),
      choose2_double (rawCount n), Nat.add_comm (2 * 2) _]

-- ═══ mod-5 dynamics ═══

/-- Multiples of 5 are `choose2`-stable mod 5. -/
theorem choose2_mul5 : ∀ k : Nat, ∃ j, choose2 (5 * k) = 5 * j
  | 0 => ⟨0, rfl⟩
  | k + 1 => by
    have ⟨j, hj⟩ := choose2_mul5 k
    refine ⟨j + 2 + k * 5, ?_⟩
    have h : 5 * (k + 1) = 5 * k + 5 := rfl
    rw [h, choose2_add (5 * k) 5, hj,
        Nat.mul_add 5 (j + 2) (k * 5), Nat.mul_add 5 j 2,
        Nat.mul_comm (5 * k) 5, Nat.mul_comm k 5]
    rfl

private theorem shift2 (A M : Nat) : 2 + (A + 1 + M) = A + M + 3 := by
  rw [Nat.add_comm 2 (A + 1 + M), Nat.add_assoc A 1 M,
      Nat.add_assoc A (1 + M) 2, Nat.add_comm 1 M,
      Nat.add_assoc M 1 2, ← Nat.add_assoc A M 3]

private theorem shift3 (A M : Nat) : 2 + (A + 3 + M) = A + M + 5 := by
  rw [Nat.add_comm 2 (A + 3 + M), Nat.add_assoc A 3 M,
      Nat.add_assoc A (3 + M) 2, Nat.add_comm 3 M,
      Nat.add_assoc M 3 2, ← Nat.add_assoc A M 5]

/-- Step `≡ 0 → ≡ 2`. -/
theorem step_zero (m k : Nat) (h : rawCount m = 5 * k) :
    ∃ j, rawCount (m + 1) = 5 * j + 2 := by
  have ⟨i, hi⟩ := choose2_mul5 k
  exact ⟨i, by rw [rawCount_succ, h, hi, Nat.add_comm]⟩

/-- Step `≡ 2 → ≡ 3`. -/
theorem step_two (m k : Nat) (h : rawCount m = 5 * k + 2) :
    ∃ j, rawCount (m + 1) = 5 * j + 3 := by
  have ⟨i, hi⟩ := choose2_mul5 k
  refine ⟨i + 2 * k, ?_⟩
  rw [rawCount_succ, h, choose2_add (5 * k) 2, hi,
      Nat.mul_add 5 i (2 * k), mul_assoc 5 k 2,
      Nat.mul_comm k 2, ← mul_assoc 5 2 k,
      Nat.mul_comm 5 2, mul_assoc 2 5 k]
  exact shift2 (5 * i) (2 * (5 * k))

/-- Step `≡ 3 → ≡ 0`. -/
theorem step_three (m k : Nat) (h : rawCount m = 5 * k + 3) :
    ∃ j, rawCount (m + 1) = 5 * j := by
  have ⟨i, hi⟩ := choose2_mul5 k
  refine ⟨i + 3 * k + 1, ?_⟩
  rw [rawCount_succ, h, choose2_add (5 * k) 3, hi,
      Nat.mul_add 5 (i + 3 * k) 1,
      Nat.mul_add 5 i (3 * k), mul_assoc 5 k 3,
      Nat.mul_comm k 3, ← mul_assoc 5 3 k,
      Nat.mul_comm 5 3, mul_assoc 3 5 k]
  exact shift3 (5 * i) (3 * (5 * k))

/-- ★★ **Pure period-3 cycle mod 5**: along the depth axis the census
    reads `(2, 3, 0)` mod 5, restarting every three levels with no
    pre-period.  (Generic self-restart — see module docstring; no
    level privileged.) -/
theorem rawCount_mod5_cycle : ∀ n : Nat,
    (∃ k, rawCount (3 * n) = 5 * k + 2)
    ∧ (∃ k, rawCount (3 * n + 1) = 5 * k + 3)
    ∧ (∃ k, rawCount (3 * n + 2) = 5 * k)
  | 0 => ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩⟩
  | n + 1 => by
    have ⟨_, _, h2⟩ := rawCount_mod5_cycle n
    have ⟨k0, hk0⟩ := h2
    have ⟨j0, hj0⟩ := step_zero (3 * n + 2) k0 hk0
    have ⟨j1, hj1⟩ := step_two (3 * n + 3) j0 hj0
    have ⟨j2, hj2⟩ := step_three (3 * n + 4) j1 hj1
    exact ⟨⟨j0, hj0⟩, ⟨j1, hj1⟩, ⟨j2, hj2⟩⟩

/-- Readout table in `%` form (via the pure mod lemmas — no core
    `%`-lemma propext). -/
theorem rawCount_mod5_table (n : Nat) :
    rawCount (3 * n) % 5 = 2
    ∧ rawCount (3 * n + 1) % 5 = 3
    ∧ rawCount (3 * n + 2) % 5 = 0 := by
  have ⟨⟨k0, h0⟩, ⟨k1, h1⟩, ⟨k2, h2⟩⟩ := rawCount_mod5_cycle n
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, Nat.add_comm (5 * k0) 2, Nat.mul_comm 5 k0]
    exact add_mul_mod_self_pure 2 5 k0
  · rw [h1, Nat.add_comm (5 * k1) 3, Nat.mul_comm 5 k1]
    exact add_mul_mod_self_pure 3 5 k1
  · rw [h2, Nat.mul_comm 5 k2]
    have := add_mul_mod_self_pure 0 5 k2
    rw [Nat.zero_add] at this
    rw [this]

end E213.Lib.Math.Foundations.UniverseChain.RawCountQuadratic
