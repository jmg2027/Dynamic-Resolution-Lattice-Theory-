import E213.Lib.Math.Foundations.UniverseChain.RawCountQuadratic
import E213.Meta.Tactic.Pow213

/-!
# Base-2 double-exponential sandwich for the Raw census (∅-axiom)

For `n ≥ 0`:

  `2^(2^(n+1))  <  rawCount (n+3)  <  2^(2^(n+2))`

strict on both sides.  **The base is 2 = NT, not d = 5**: the census
tower lives in the `d = 2` slice of the parametric family
`configCountD d n = d^(d^n)` (`Lib/Math/Cohomology/Fractal/
ConfigCount.lean`); the resemblance to the `d = 5` slice is shape
only.  Engine: the doubled identity `2·(2 + C(T,2)) + T = T² + 4`
(`choose2_double`), squeezed between `(2M+1)² ≥ 4M² + …` (lower) and
`(T+1)² ≤ M²` (upper).
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawCountBounds

open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence
  (choose2 rawCount)
open E213.Lib.Math.Foundations.UniverseChain.RawCountQuadratic
  (choose2_double)
open E213.Tactic.NatHelper
open E213.Tactic.Pow213

-- ═══ cancellation helpers (pure) ═══

private theorem half_le {a b : Nat} (h : 2 * a ≤ 2 * b) : a ≤ b :=
  match Nat.lt_or_ge b a with
  | Or.inr hge => hge
  | Or.inl hlt =>
    have h2 : 2 * (b + 1) ≤ 2 * a := Nat.mul_le_mul_left 2 hlt
    have h3 : 2 * b + 2 ≤ 2 * b := by
      have := Nat.le_trans h2 h
      rw [Nat.mul_add 2 b 1] at this
      exact this
    absurd (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) h3)
      (Nat.lt_irrefl (2 * b))

private theorem half_lt {a b : Nat} (h : 2 * a < 2 * b) : a < b :=
  match Nat.lt_or_ge a b with
  | Or.inl hlt => hlt
  | Or.inr hge =>
    absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left 2 hge))
      (Nat.lt_irrefl (2 * a))

private theorem add_cancel_le {a b c : Nat} (h : a + c ≤ b + c) :
    a ≤ b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact le_of_add_le_add_left h

private theorem add_cancel_lt {a b c : Nat} (h : a + c < b + c) :
    a < b := by
  have h' : (a + 1) + c ≤ b + c := by
    rw [Nat.add_assoc a 1 c, Nat.add_comm 1 c, ← Nat.add_assoc a c 1]
    exact h
  exact add_cancel_le h'

/-- The doubled census identity: `2·(2 + C(T,2)) + T = T² + 4`. -/
private theorem doubled_id (T : Nat) :
    2 * (2 + choose2 T) + T = T * T + 4 := by
  rw [Nat.mul_add 2 2 (choose2 T),
      Nat.add_assoc (2 * 2) (2 * choose2 T) T,
      choose2_double T, Nat.add_comm (2 * 2) (T * T)]

-- ═══ the two squeeze steps (parametric in M) ═══

/-- Lower squeeze: `T ≥ 2M + 1 ⟹ 2 + C(T,2) ≥ 2M² + 1`. -/
theorem census_step_lower (T M : Nat) (hM : 1 ≤ M)
    (hT : 2 * M + 1 ≤ T) : 2 * (M * M) + 1 ≤ 2 + choose2 T := by
  apply half_le
  apply add_cancel_le (c := T)
  rw [doubled_id T]
  have h2M : 2 ≤ 2 * M := by
    have := Nat.mul_le_mul_left 2 hM
    rwa [Nat.mul_one] at this
  calc 2 * (2 * (M * M) + 1) + T
      = 2 * (2 * (M * M)) + 2 + T := by
        rw [Nat.mul_add 2 (2 * (M * M)) 1]
    _ ≤ 2 * (2 * (M * M)) + 2 * M + T :=
        Nat.add_le_add_right (Nat.add_le_add_left h2M _) T
    _ = (2 * M) * (2 * M) + 2 * M + T := by
        rw [mul_assoc 2 M (2 * M), mul_left_comm M 2 M]
    _ = (2 * M + 1) * (2 * M) + T := by
        rw [add_mul (2 * M) 1 (2 * M), Nat.one_mul]
    _ ≤ T * (2 * M) + T :=
        Nat.add_le_add_right (Nat.mul_le_mul_right (2 * M) hT) T
    _ = T * (2 * M + 1) := by rw [Nat.mul_add T (2 * M) 1, Nat.mul_one]
    _ ≤ T * T := Nat.mul_le_mul_left T hT
    _ ≤ T * T + 4 := Nat.le_add_right (T * T) 4

/-- Upper squeeze: `T < M ⟹ 2 + C(T,2) < M²` (for `M ≥ 2`). -/
theorem census_step_upper (T M : Nat) (hM : 2 ≤ M)
    (hT : T + 1 ≤ M) : 2 + choose2 T < M * M := by
  apply half_lt
  apply add_cancel_lt (c := T)
  rw [doubled_id T]
  have u2 : T * T + 1 ≤ (T + 1) * (T + 1) := by
    rw [add_mul T 1 (T + 1), Nat.one_mul, Nat.mul_add T T 1,
        Nat.mul_one, Nat.add_assoc (T * T) T (T + 1)]
    have h01 : (1 : Nat) ≤ T + 1 := Nat.succ_le_succ (Nat.zero_le T)
    exact Nat.add_le_add_left
      (Nat.le_trans h01 (Nat.le_add_left (T + 1) T)) (T * T)
  have u3 : T * T + 4 ≤ M * M + 3 :=
    Nat.add_le_add_right (Nat.le_trans u2 (Nat.mul_le_mul hT hT)) 3
  have u4 : M * M + 3 < 2 * (M * M) + T := by
    rw [two_mul (M * M), Nat.add_assoc (M * M) (M * M) T]
    apply Nat.add_lt_add_left
    exact Nat.lt_of_lt_of_le (by decide : (3 : Nat) < 4)
      (Nat.le_trans (Nat.mul_le_mul hM hM)
        (Nat.le_add_right (M * M) T))
  exact lt_of_le_lt u3 u4

-- ═══ the sandwich ═══

private theorem two_le_two_pow : {k : Nat} → 1 ≤ k → 2 ≤ 2 ^ k
  | k + 1, _ => by
    have h2 : 1 * 2 ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 (one_le_two_pow k)
    rw [Nat.one_mul] at h2
    rw [Nat.pow_succ]
    exact h2

/-- ★ Lower bound, sharp at the base: `2^(2^n + 1) + 1 ≤ rawCount
    (n+2)`, with equality at `n = 0` (both sides 5). -/
theorem rawCount_lower : ∀ n : Nat,
    2 ^ (2 ^ n + 1) + 1 ≤ rawCount (n + 2)
  | 0 => by decide
  | n + 1 => by
    have ihT : 2 * 2 ^ 2 ^ n + 1 ≤ rawCount (n + 2) := by
      rw [Nat.mul_comm 2 (2 ^ 2 ^ n), ← Nat.pow_succ 2 (2 ^ n)]
      exact rawCount_lower n
    have step := census_step_lower (rawCount (n + 2)) (2 ^ 2 ^ n)
      (one_le_two_pow (2 ^ n)) ihT
    have e2 : (2 : Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm, two_mul]
    rw [e2, Nat.pow_succ 2 (2 ^ n + 2 ^ n), pow_add_two (2 ^ n) (2 ^ n),
        Nat.mul_comm (2 ^ 2 ^ n * 2 ^ 2 ^ n) 2]
    exact step

/-- ★ Upper bound, strict: `rawCount (n+3) < 2^(2^(n+2))`. -/
theorem rawCount_upper : ∀ n : Nat, rawCount (n + 3) < 2 ^ 2 ^ (n + 2)
  | 0 => by decide
  | n + 1 => by
    have step := census_step_upper (rawCount (n + 3)) (2 ^ 2 ^ (n + 2))
      (two_le_two_pow (one_le_two_pow (n + 2))) (rawCount_upper n)
    have e2 : (2 : Nat) ^ (n + 3) = 2 ^ (n + 2) + 2 ^ (n + 2) := by
      rw [Nat.pow_succ, Nat.mul_comm, two_mul]
    rw [e2, pow_add_two (2 ^ (n + 2)) (2 ^ (n + 2))]
    exact step

/-- ★★★ **Base-2 sandwich** (strict both sides):
    `2^(2^(n+1)) < rawCount (n+3) < 2^(2^(n+2))`.

    In the parametric family this is
    `configCountD 2 (n+1) < rawCount (n+3) < configCountD 2 (n+2)`
    — the census tower is graded by the `d = 2 = NT` slice, not the
    `d = 5` slice; `log₂ log₂ rawCount` advances one per depth. -/
theorem rawCount_sandwich (n : Nat) :
    2 ^ 2 ^ (n + 1) < rawCount (n + 3)
    ∧ rawCount (n + 3) < 2 ^ 2 ^ (n + 2) := by
  refine ⟨?_, rawCount_upper n⟩
  have hp : 2 ^ 2 ^ (n + 1) < 2 ^ (2 ^ (n + 1) + 1) + 1 :=
    Nat.lt_of_lt_of_le (pow_lt_succ (2 ^ (n + 1))) (Nat.le_add_right _ 1)
  exact lt_of_lt_le hp (rawCount_lower (n + 1))

/-- Concrete witness row: `4 < 12 < 16` and `16 < 68 < 256`. -/
theorem rawCount_sandwich_witness :
    2 ^ 2 ^ 1 < rawCount 3 ∧ rawCount 3 < 2 ^ 2 ^ 2
    ∧ 2 ^ 2 ^ 2 < rawCount 4 ∧ rawCount 4 < 2 ^ 2 ^ 3 := by decide

end E213.Lib.Math.Foundations.UniverseChain.RawCountBounds
