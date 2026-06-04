import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberSystems.Irrational.Sqrt2KernelFree
import E213.Lib.Math.NumberSystems.Real213.FibCassiniNat

/-!
# GoldenFormMarkov — the golden form is anisotropic, and the Markov value is `√5`

The `P = [[2,1],[1,1]]` spiral invariant is the **golden form** `Q(m,k) = m² − mk − k²`
(`SpiralRotationInvariant`, `FloorReferenceForm`), discriminant `5 = NS + NT`, indefinite.
This file proves it is **anisotropic** over `ℕ`: `Q(m,k) = 0` only at the origin — i.e.
`m² = mk + k²` forces `m = k = 0`.  The proof is a Vieta descent `(m,k) ↦ (k, m−k)` (no
`mod 5`, no `omega`, fuel-bounded structural induction like the repo's √2 proof).

**Why this is the Markov-spectrum minimum.**  An indefinite binary quadratic form `Q` of
discriminant `D` has Markov value `M(Q) = √D / inf_{(m,k)≠0} |Q(m,k)|`.  For the golden form
`D = 5`, and anisotropy + `Q(1,0) = 1` give `inf|Q| = 1`, so `M(Q) = √5`.  This is the
**smallest** value of the Lagrange/Markov spectrum — the constant of the *worst-approximable*
number, the golden ratio φ = [1;1,1,…], whose Fibonacci convergents carry the Cassini
det-one floor `W = ±1`.  So the repo's golden form is the **first Markov form**, the `W = ±1`
floor *is* the form taking its minimum `±1`, and √5 is the Lagrange minimum — the bottom of
the approximation spectrum, read off the spiral invariant.  (The Markov-value formula and
"√5 = Lagrange minimum" are classical; the ∅-axiom content here is `D = 5`, anisotropy, and
`inf|Q| = 1`.)
-/

namespace E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov

/-! ## §0 — pure square-monotonicity (core `Nat.mul_lt_mul_right` is an `Iff` that leaks
`propext`/`Classical.choice`/`Quot.sound`) -/

/-- Pure left-cancellation `a + b = a + c → b = c` (core `Nat.add_left_cancel` leaks
    `propext`). -/
theorem add_left_cancel_pure : ∀ (a b c : Nat), a + b = a + c → b = c
  | 0, _, _, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | a + 1, b, c, h => by
      apply add_left_cancel_pure a
      rw [Nat.succ_add, Nat.succ_add] at h
      exact Nat.succ.inj h

/-- `m < k → m² < k²` over `ℕ`, ∅-axiom. -/
theorem sq_lt_sq (m k : Nat) (h : m < k) : m * m < k * k := by
  have hk1 : m + 1 ≤ k := h
  have hkpos : 0 < k := Nat.lt_of_lt_of_le (Nat.succ_pos m) hk1
  have h1 : m * m ≤ m * k := Nat.mul_le_mul_left m (Nat.le_of_lt h)
  have hmk : (m + 1) * k ≤ k * k := Nat.mul_le_mul_right k hk1
  rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul] at hmk
  have h2 : m * k < k * k := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hkpos) hmk
  exact Nat.lt_of_le_of_lt h1 h2

/-! ## §1 — Vieta descent: the golden form is anisotropic over `ℕ` -/

/-- Fuel-bounded descent.  `m² = mk + k²` with `k ≤ n` forces `k = 0`.  The substitution
    `m = k + r` turns the equation into `k² = kr + r²` with `r < k` — the same form one
    level down — so a structural induction on the fuel `n` closes it. -/
theorem golden_aux : ∀ (n k m : Nat), k ≤ n → m * m = m * k + k * k → k = 0 := by
  intro n
  induction n with
  | zero => intro k m hkn _; exact Nat.le_zero.mp hkn
  | succ n ih =>
    intro k m hkn heq
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact hk0
    · -- k ≥ 1: descend to r = m − k < k
      have hge : k ≤ m := by
        rcases Nat.lt_or_ge m k with h | h
        · have hle : k * k ≤ m * m := by rw [heq]; exact Nat.le_add_left (k * k) (m * k)
          exact absurd (Nat.lt_of_lt_of_le (sq_lt_sq m k h) hle)
            (Nat.lt_irrefl (m * m))
        · exact h
      obtain ⟨r, hr⟩ := Nat.le.dest hge
      subst hr
      have key : k * r + r * r = k * k := by
        have h1 : (k + r) * (k + r) = (k * k + k * r) + (k * r + r * r) := by
          rw [Nat.mul_add, E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.add_mul, Nat.mul_comm r k]
        have h2 : (k + r) * k + k * k = (k * k + k * r) + k * k := by
          rw [E213.Tactic.NatHelper.add_mul, Nat.mul_comm r k]
        rw [h1, h2] at heq
        exact add_left_cancel_pure _ _ _ heq
      have hrlt : r < k := by
        rcases Nat.lt_or_ge r k with h | h
        · exact h
        · have h1 : k * k ≤ k * r := Nat.mul_le_mul_left k h
          have hr1 : 1 ≤ r := Nat.le_trans hkpos h
          have h2 : 1 ≤ r * r := Nat.mul_le_mul hr1 hr1
          have hcontra : k * k + 1 ≤ k * r + r * r := Nat.add_le_add h1 h2
          rw [key] at hcontra
          exact absurd hcontra (Nat.not_succ_le_self (k * k))
      have hrn : r ≤ n := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrlt hkn)
      have hr0 : r = 0 := ih r k hrn key.symm
      -- r = 0 ⟹ k² = 0 ⟹ contradiction with k ≥ 1
      rw [hr0, Nat.mul_zero, Nat.mul_zero, Nat.zero_add] at key
      have hk1 : 1 ≤ k * k := Nat.mul_le_mul hkpos hkpos
      rw [← key] at hk1
      exact absurd hk1 (by decide)

/-- ★★★ **The golden form is anisotropic over `ℕ`.**  `m² = mk + k²` (i.e. `Q(m,k) = 0`)
    forces `m = k = 0`: the form represents `0` only trivially.  Hence `|Q| ≥ 1` on every
    non-zero `(m,k)`, and with `Q(1,0) = 1` the minimum is exactly `1`. -/
theorem golden_anisotropic (m k : Nat) (heq : m * m = m * k + k * k) : m = 0 ∧ k = 0 := by
  have hk : k = 0 := golden_aux k k m (Nat.le_refl k) heq
  subst hk
  rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero] at heq
  -- heq : m * m = 0
  refine ⟨?_, rfl⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact hm0
  · have : 1 ≤ m * m := Nat.mul_le_mul hmpos hmpos
    rw [heq] at this
    exact absurd this (by decide)

/-! ## §2 — the Markov data: discriminant 5, minimum 1, value √5 -/

/-- The golden form represents `1` at `(1,0)`: `1² = 1·0 + 0² + 1`.  With anisotropy this
    pins `inf|Q| = 1`, hence Markov value `M(Q) = √(disc)/inf|Q| = √5/1 = √5` (cited). -/
theorem golden_represents_one : (1 : Nat) * 1 = 1 * 0 + 0 * 0 + 1 := by decide

/-- ★★★★ **The golden form is the first Markov form (Markov value `√5`).**  Bundles the
    ∅-axiom data: anisotropy (`Q = 0` only at the origin, so `inf|Q| = 1`) and `Q(1,0) = 1`.
    With discriminant `5`, the Markov value is `√5` — the minimum of the Lagrange/Markov
    spectrum, the worst-approximable constant of φ (whose Cassini convergents carry the
    `W = ±1` floor `= the form's minimum`). -/
theorem golden_first_markov_form :
    (∀ m k : Nat, m * m = m * k + k * k → m = 0 ∧ k = 0)
    ∧ (1 : Nat) * 1 = 1 * 0 + 0 * 0 + 1 :=
  ⟨golden_anisotropic, golden_represents_one⟩

open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)

/-- ★★★ **The minimum is attained on φ's convergents — the `W = ±1` floor is the form's
    minimum.**  On every Fibonacci convergent pair, the golden form takes value `−1`:
    `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) + fib(2n+1)²` (i.e. `Q(fib(2n+2), fib(2n+1)) = −1`),
    which is exactly the Cassini relation (`FibCassiniNat.fib_cassini_norm`).  With anisotropy
    (`|Q| ≥ 1`) this shows `inf|Q| = 1` is **attained** precisely along φ's Fibonacci
    convergents — the `W = ±1` cross-determinant floor *is* the golden form's minimum, the
    Markov/Lagrange value `√5` realised on the worst-approximable number. -/
theorem golden_min_attained_on_fib (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 2) + 1
    = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1) :=
  E213.Lib.Math.NumberSystems.Real213.FibCassiniNat.fib_cassini_norm n

/-! ## §3 — the second Markov value `√8`: the `√2` form `x² − 2y²` (disc 8) -/

/-- ★★★ **The `√2` form `x² − 2y²` (disc 8) is anisotropic over `ℕ`.**  `x² = 2y²` forces
    `x = y = 0` — reusing the repo's `∅`-axiom `√2` irrationality (`sqrt2_irrational`). -/
theorem silver_anisotropic (x y : Nat) (h : x * x = 2 * (y * y)) : x = 0 ∧ y = 0 := by
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · subst hy0
    refine ⟨?_, rfl⟩
    have h' : x * x = 0 := h
    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
    · exact hx0
    · have : 1 ≤ x * x := Nat.mul_le_mul hxpos hxpos
      rw [h'] at this
      exact absurd this (by decide)
  · exact absurd h (E213.Lib.Math.NumberSystems.Irrational.Sqrt2KernelFree.sqrt2_irrational y hypos x)

/-- ★★★★ **The `√2` form is the second Markov form (Markov value `√8 = 2√2`).**  Anisotropy
    (`inf|x²−2y²| = 1`, attained at `(1,0)`) with discriminant `8` gives Markov value `√8` —
    the second value of the Lagrange/Markov spectrum, the constant of `√2 = [1;2,2,…]`.  So
    the repo's first two indefinite forms (golden disc 5, silver disc 8) realise the first
    two spectrum values `√5, √8` — read off the two `∅`-axiom irrational seeds. -/
theorem silver_second_markov_form :
    (∀ x y : Nat, x * x = 2 * (y * y) → x = 0 ∧ y = 0)
    ∧ (1 : Nat) * 1 = 2 * (0 * 0) + 1 :=
  ⟨silver_anisotropic, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov
