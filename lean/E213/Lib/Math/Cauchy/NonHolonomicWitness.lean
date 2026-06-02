import E213.Lib.Math.Cauchy.HurwitzianCF
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# A genuinely non-holonomic witness — refuting the Klazar growth majorant

`HurwitzianCF` tops out at "non-Hurwitzian" (`2ⁿ`), which is *still holonomic* (C-finite).
This file builds the next tier — a sequence that is **genuinely non-holonomic** (no
polynomial-coefficient linear recurrence governs it) — ∅-axiom, via the elementary form of
**Klazar's growth bound** (holonomic ⟹ `|aₙ| ≤ cⁿ·(n!)^d`).

## The growth majorant (eventually)

A ℕ-valued P-recursive sequence `p_k(n)·a_{n+k} = Σ_{i<k} p_i(n)·a_{n+i}` (`pᵢ ∈ ℤ[n]`,
`p_k ≠ 0`) satisfies, at every `n` past the **finitely many roots** of `p_k` (so
`|p_k(n)| ≥ 1`), the integer triangle bound
`a_{n+k} = |Σ p_i a_{n+i}| / |p_k| ≤ Σ |p_i(n)|·a_{n+i} ≤ C·(n+1)^D · windowSum`.  The root
exceptions force an **eventual** quantifier — without it a singular-but-holonomic sequence
would be falsely certified.  So:

  `HolonomicGrowth s := ∃ k C D N, 1 ≤ k ∧ ∀ n ≥ N, s(n+k) ≤ C·(n+1)^D · windowSum k s n`.

Thus **holonomic ⟹ `HolonomicGrowth`** (the interpretive bridge, classical — Klazar's
direction), and therefore `¬ HolonomicGrowth s ⟹ s` is **not** P-recursive.  The certificate
is *one-directional* (sufficient, not a characterisation): `HolonomicGrowth` is strictly
weaker than P-recursive, so it cannot detect *every* non-holonomic sequence — only certify the
ones whose growth beats the envelope.

## The envelope

`holonomicGrowth_envelope` proves the Klazar envelope ∅-axiom by **window-sum telescoping**
(`windowSum k s (n+1) ≤ (C+1)(n+1)^D · windowSum k s n`, no `ℕ` truncation):

  `HolonomicGrowth-via-(k,C,D,N) ⟹ ∀ m, windowSum k s (N+m) ≤ windowSum k s N · (C+1)ᵐ · (N+m)!^D`.

A super-factorial witness then beats every envelope (`NonHolonomicWitness.lean` §3, to follow).

All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.NonHolonomicWitness

/-! ## §0 — pure `ℕ` arithmetic (core `Nat.mul_pow`, `Nat.mul_lt_mul_left`, `Nat.add_mul`
leak `propext`/`Classical`; local pure replacements) -/

/-- `1 ≤ b ⟹ 1 ≤ bᵉ` (pure). -/
theorem one_le_pow (b e : Nat) (hb : 1 ≤ b) : 1 ≤ b ^ e := by
  induction e with
  | zero => exact Nat.le_refl 1
  | succ e ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul ih hb

/-- Pure `(a·b)^D = a^D · b^D` (core `Nat.mul_pow` leaks `propext`). -/
theorem mul_pow_pure (a b : Nat) : ∀ D, (a * b) ^ D = a ^ D * b ^ D := by
  intro D
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [Nat.pow_succ, ih, Nat.pow_succ, Nat.pow_succ,
        E213.Tactic.NatHelper.mul_mul_mul_comm_213]

/-- Four-factor commutation: `R·A·(P·Q) = A·P·(R·Q)` (pure, via `mul_assoc`/`mul_left_comm`). -/
theorem four_comm (R A P Q : Nat) : R * A * (P * Q) = A * P * (R * Q) := by
  rw [Nat.mul_comm R A, E213.Tactic.NatHelper.mul_assoc A R (P * Q),
      E213.Tactic.NatHelper.mul_left_comm R P Q,
      ← E213.Tactic.NatHelper.mul_assoc A P (R * Q)]

/-! ## §1 — the window sum and its forward shift -/

/-- `windowSum k s n = s n + s(n+1) + … + s(n+k-1)` (the `k`-term window from `n`). -/
def windowSum : Nat → (Nat → Nat) → Nat → Nat
  | 0,   _, _ => 0
  | k+1, s, n => s n + windowSum k s (n + 1)

/-- A summand is below its window: `s n ≤ windowSum (k+1) s n`. -/
theorem le_windowSum (k : Nat) (s : Nat → Nat) (n : Nat) : s n ≤ windowSum (k + 1) s n :=
  Nat.le_add_right (s n) (windowSum k s (n + 1))

/-- The window's forward shift, subtraction-free:
    `windowSum k s n + s(n+k) = s n + windowSum k s (n+1)`. -/
theorem windowSum_shift (k : Nat) (s : Nat → Nat) :
    ∀ n, windowSum k s n + s (n + k) = s n + windowSum k s (n + 1) := by
  induction k with
  | zero =>
    intro n
    show (0 : Nat) + s (n + 0) = s n + 0
    rw [Nat.add_zero, Nat.zero_add, Nat.add_zero]
  | succ k ih =>
    intro n
    show (s n + windowSum k s (n + 1)) + s (n + (k + 1))
        = s n + (s (n + 1) + windowSum k s (n + 2))
    have e : n + (k + 1) = (n + 1) + k :=
      (Nat.add_succ n k).trans (Nat.succ_add n k).symm
    rw [e, Nat.add_assoc (s n) (windowSum k s (n + 1)) (s ((n + 1) + k)), ih (n + 1)]

/-- One telescoping step: `windowSum k s (n+1) ≤ windowSum k s n + s(n+k)`. -/
theorem windowSum_step_le (k : Nat) (s : Nat → Nat) (n : Nat) :
    windowSum k s (n + 1) ≤ windowSum k s n + s (n + k) := by
  rw [windowSum_shift k s n]
  exact Nat.le_add_left _ _

/-! ## §2 — the holonomic growth majorant and its Klazar envelope -/

/-- `fact n = n!` (local, to keep this file Lens-independent). -/
def fact : Nat → Nat
  | 0   => 1
  | n+1 => (n + 1) * fact n

/-- `1 ≤ n!`. -/
theorem fact_pos (n : Nat) : 1 ≤ fact n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n ih =>
    show 1 ≤ (n + 1) * fact n
    exact Nat.mul_le_mul (Nat.succ_pos n) ih

/-- `s` is bounded by a polynomial-coefficient linear majorant of order `k`, eventually:
    `∃ N, ∀ n ≥ N, s(n+k) ≤ C·(n+1)^D · windowSum k s n`.  The ∅-axiom shadow of "holonomic"
    (every ℕ-valued P-recursive sequence satisfies one past the roots of its leading
    coefficient — Klazar's direction, cited). -/
def HolonomicGrowth (s : Nat → Nat) : Prop :=
  ∃ k C D N, 1 ≤ k ∧ ∀ n, N ≤ n → s (n + k) ≤ C * (n + 1) ^ D * windowSum k s n

/-- The per-step contraction of the window from a single majorant inequality at `n`. -/
theorem windowSum_contract (k C D : Nat) (s : Nat → Nat) (n : Nat)
    (hrn : s (n + k) ≤ C * (n + 1) ^ D * windowSum k s n) :
    windowSum k s (n + 1) ≤ (C + 1) * (n + 1) ^ D * windowSum k s n := by
  have hstep : windowSum k s (n + 1) ≤ windowSum k s n + s (n + k) := windowSum_step_le k s n
  have hcombine : windowSum k s n + s (n + k)
      ≤ windowSum k s n + C * (n + 1) ^ D * windowSum k s n :=
    Nat.add_le_add_left hrn (windowSum k s n)
  have hfold : windowSum k s n + C * (n + 1) ^ D * windowSum k s n
      = (1 + C * (n + 1) ^ D) * windowSum k s n := by
    rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul]
  have hpoly : (1 + C * (n + 1) ^ D) * windowSum k s n
      ≤ (C + 1) * (n + 1) ^ D * windowSum k s n := by
    refine Nat.mul_le_mul ?_ (Nat.le_refl (windowSum k s n))
    rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul, Nat.add_comm 1 (C * (n + 1) ^ D)]
    exact Nat.add_le_add_left (one_le_pow (n + 1) D (Nat.succ_le_succ (Nat.zero_le n)))
      (C * (n + 1) ^ D)
  exact Nat.le_trans hstep (Nat.le_trans hcombine (hfold ▸ hpoly))

/-- The envelope multiplier `env C D N m = (C+1)ᵐ · ((N+m)!)^D`. -/
def env (C D N m : Nat) : Nat := (C + 1) ^ m * (fact (N + m)) ^ D

/-- `env` satisfies the same recurrence as the contraction factor. -/
theorem env_succ (C D N m : Nat) :
    env C D N (m + 1) = (C + 1) * (N + m + 1) ^ D * env C D N m := by
  show (C + 1) ^ (m + 1) * (fact (N + (m + 1))) ^ D
      = (C + 1) * (N + m + 1) ^ D * ((C + 1) ^ m * (fact (N + m)) ^ D)
  have hN : N + (m + 1) = (N + m) + 1 := (Nat.add_assoc N m 1).symm
  rw [hN]
  show (C + 1) ^ (m + 1) * ((N + m + 1) * fact (N + m)) ^ D
      = (C + 1) * (N + m + 1) ^ D * ((C + 1) ^ m * (fact (N + m)) ^ D)
  rw [mul_pow_pure (N + m + 1) (fact (N + m)) D, Nat.pow_succ]
  -- (C+1)^m * (C+1) * ((N+m+1)^D * (fact (N+m))^D)
  --   = (C+1) * (N+m+1)^D * ((C+1)^m * (fact (N+m))^D)
  exact four_comm ((C + 1) ^ m) (C + 1) ((N + m + 1) ^ D) ((fact (N + m)) ^ D)

/-- ★★★ **The Klazar envelope (∅-axiom).**  Past the threshold `N`, a `(k,C,D)` holonomic
    majorant forces the window under `windowSum k s N · (C+1)ᵐ · ((N+m)!)^D`. -/
theorem holonomicGrowth_envelope (k C D N : Nat) (s : Nat → Nat)
    (hrec : ∀ n, N ≤ n → s (n + k) ≤ C * (n + 1) ^ D * windowSum k s n) :
    ∀ m, windowSum k s (N + m) ≤ windowSum k s N * env C D N m := by
  intro m
  induction m with
  | zero =>
    show windowSum k s (N + 0) ≤ windowSum k s N * env C D N 0
    rw [Nat.add_zero]
    show windowSum k s N ≤ windowSum k s N * ((C + 1) ^ 0 * (fact (N + 0)) ^ D)
    rw [Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    -- W_N ≤ W_N * (fact N)^D, since (fact N)^D ≥ 1
    calc windowSum k s N = windowSum k s N * 1 := (Nat.mul_one _).symm
      _ ≤ windowSum k s N * (fact N) ^ D :=
          Nat.mul_le_mul (Nat.le_refl (windowSum k s N))
            (one_le_pow (fact N) D (fact_pos N))
  | succ m ih =>
    have hcon : windowSum k s (N + m + 1)
        ≤ (C + 1) * (N + m + 1) ^ D * windowSum k s (N + m) :=
      windowSum_contract k C D s (N + m) (hrec (N + m) (Nat.le_add_right N m))
    have hmono : (C + 1) * (N + m + 1) ^ D * windowSum k s (N + m)
        ≤ (C + 1) * (N + m + 1) ^ D * (windowSum k s N * env C D N m) :=
      Nat.mul_le_mul (Nat.le_refl _) ih
    show windowSum k s (N + (m + 1)) ≤ windowSum k s N * env C D N (m + 1)
    have hNm : N + (m + 1) = N + m + 1 := (Nat.add_assoc N m 1).symm
    rw [hNm, env_succ]
    -- (C+1)(N+m+1)^D · (W_N · env m) = W_N · ((C+1)(N+m+1)^D · env m)
    exact Nat.le_trans hcon (Nat.le_trans hmono (Nat.le_of_eq
      (E213.Tactic.NatHelper.mul_left_comm ((C + 1) * (N + m + 1) ^ D)
        (windowSum k s N) (env C D N m))))

/-- `s n` itself, past `N`, is under the envelope (combine `le_windowSum`). -/
theorem holonomicGrowth_value_bound {k C D N : Nat} {s : Nat → Nat} (hk : 1 ≤ k)
    (hrec : ∀ n, N ≤ n → s (n + k) ≤ C * (n + 1) ^ D * windowSum k s n) (m : Nat) :
    s (N + m) ≤ windowSum k s N * env C D N m := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero => exact absurd hk (by decide)
    | succ k' => exact ⟨k', rfl⟩
  exact Nat.le_trans (le_windowSum k' s (N + m))
    (holonomicGrowth_envelope (k' + 1) C D N s hrec m)

end E213.Lib.Math.Cauchy.NonHolonomicWitness
