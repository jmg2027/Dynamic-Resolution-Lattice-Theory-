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

## The witness

`superFact n = (n!)ⁿ` beats every envelope: `envelope_exceeded` picks, for any `(W,C,D,N)`, an
`m` with `W·(C+1)ᵐ·((N+m)!)^D < ((N+m)!)^(N+m)` (take `B = W+C+D+2`, `m = 2B²+2`; then
`F = (N+m)!` has `B² ≤ F`, so the whole envelope fits under `F^(B²+D+2)` while the witness is
`F^(N+m)` with `B²+D+2 < N+m`).  Hence **`superFact_nonHolonomic : ¬ HolonomicGrowth superFact`** —
the first ∅-axiom certificate of *non-holonomicity proper*, strictly above the
non-Hurwitzian-but-C-finite `2ⁿ` of `HurwitzianCF.geometric_not_quasipoly`.

All ∅-axiom (`22 pure / 0 dirty`).
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

/-- Pure strict left multiplication: `1 ≤ c → a < b → c*a < c*b`. -/
theorem mul_lt_mul_left_pure {a b c : Nat} (hc : 1 ≤ c) (h : a < b) : c * a < c * b := by
  have h1 : c * (a + 1) ≤ c * b := Nat.mul_le_mul_left c h
  have h2 : c * a + 1 ≤ c * (a + 1) := by
    rw [Nat.mul_succ]; exact Nat.add_le_add_left hc (c * a)
  exact Nat.lt_of_lt_of_le h2 h1

/-- Pure `a^(m·n) = (a^m)^n` (core `Nat.pow_mul` leaks `propext`). -/
theorem pow_mul_pure (a m : Nat) : ∀ n, a ^ (m * n) = (a ^ m) ^ n := by
  intro n
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ n ih => rw [Nat.mul_succ, E213.Meta.Nat.PureNat.pow_add, ih, Nat.pow_succ]

/-- Pure strict power monotonicity in the exponent: `2 ≤ b → e < f → bᵉ < bᶠ`. -/
theorem pow_lt_pow_right_pure {b e f : Nat} (hb : 2 ≤ b) (h : e < f) : b ^ e < b ^ f := by
  have hfe : e + (f - e) = f := E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt h)
  have hd : 1 ≤ f - e := E213.Tactic.NatHelper.le_pred_of_succ_le h
  have hbfe : b ≤ b ^ (f - e) := by
    have hp := Nat.pow_le_pow_right (Nat.le_trans (by decide) hb) hd
    rwa [Nat.pow_one] at hp
  have h1 : 1 < b ^ (f - e) :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide) hb) hbfe
  calc b ^ e = b ^ e * 1 := (Nat.mul_one _).symm
    _ < b ^ e * b ^ (f - e) := mul_lt_mul_left_pure (one_le_pow b e (Nat.le_trans (by decide) hb)) h1
    _ = b ^ (e + (f - e)) := (E213.Meta.Nat.PureNat.pow_add b e (f - e)).symm
    _ = b ^ f := by rw [hfe]

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

/-- `n ≤ n!` (each factor `≥ 1`). -/
theorem le_fact (n : Nat) : n ≤ fact n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    show n + 1 ≤ (n + 1) * fact n
    calc n + 1 = (n + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (n + 1) * fact n := Nat.mul_le_mul (Nat.le_refl _) (fact_pos n)

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

/-! ## §3 — the witness: `superFact n = (n!)ⁿ` beats every envelope -/

/-- The super-factorial witness `n ↦ (n!)ⁿ`. -/
def superFact (n : Nat) : Nat := (fact n) ^ n

/-- ★★★ **Every Klazar envelope is eventually exceeded by `(N+m)!^(N+m)`.**  For any
    constants `W, C, D, N`, there is an `m` with
    `W · (C+1)ᵐ · ((N+m)!)^D < ((N+m)!)^(N+m)`.  (Pick `m = 2·B²+2`, `B = W+C+D+2`; then
    `F := (N+m)!` satisfies `B² ≤ F`, so the entire envelope fits under `F^(B²+D+2)`, while
    the witness is `F^(N+m)` with `B²+D+2 < N+m`.) -/
theorem envelope_exceeded (W C D N : Nat) :
    ∃ m, W * ((C + 1) ^ m * (fact (N + m)) ^ D) < (fact (N + m)) ^ (N + m) := by
  obtain ⟨B, hB⟩ : ∃ B, B = W + C + D + 2 := ⟨_, rfl⟩
  refine ⟨2 * B ^ 2 + 2, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * B ^ 2 + 2 := ⟨_, rfl⟩
  rw [← hm]
  obtain ⟨F, hF⟩ : ∃ F, F = fact (N + m) := ⟨_, rfl⟩
  rw [← hF]
  -- B-bounds
  have hB2 : 2 ≤ B := by rw [hB]; exact Nat.le_add_left 2 (W + C + D)
  have hWB : W ≤ B := by
    rw [hB]
    exact Nat.le_trans (Nat.le_add_right W C)
      (Nat.le_trans (Nat.le_add_right (W + C) D) (Nat.le_add_right (W + C + D) 2))
  have hDB : D ≤ B := by
    rw [hB]
    exact Nat.le_trans (Nat.le_add_left D (W + C)) (Nat.le_add_right (W + C + D) 2)
  have hCB : C + 1 ≤ B := by
    have hC' : C ≤ W + C + D :=
      Nat.le_trans (Nat.le_add_left C W) (Nat.le_add_right (W + C) D)
    rw [hB]
    exact Nat.le_trans (Nat.add_le_add_right hC' 1)
      (Nat.add_le_add_left (by decide) (W + C + D))
  -- B ≤ B² and B < B²
  have hsq_eq : B ^ 2 = B * B := by rw [Nat.pow_succ, Nat.pow_one]
  have hBsq : B ≤ B ^ 2 := by
    rw [hsq_eq]
    calc B = B * 1 := (Nat.mul_one B).symm
      _ ≤ B * B := Nat.mul_le_mul (Nat.le_refl B) (Nat.le_trans (by decide) hB2)
  have hBltsq : B < B ^ 2 := by
    rw [hsq_eq]
    calc B = B * 1 := (Nat.mul_one B).symm
      _ < B * B := mul_lt_mul_left_pure (Nat.le_trans (by decide) hB2)
            (Nat.lt_of_lt_of_le (by decide) hB2)
  -- B² ≤ m ≤ N+m ≤ F
  have hsqm : B ^ 2 ≤ m := by
    rw [hm, E213.Tactic.NatHelper.two_mul]
    exact Nat.le_trans (Nat.le_add_right (B ^ 2) (B ^ 2)) (Nat.le_add_right (B ^ 2 + B ^ 2) 2)
  have hmF : m ≤ N + m := Nat.le_add_left m N
  have hNF : N + m ≤ F := by rw [hF]; exact le_fact (N + m)
  have hsqF : B ^ 2 ≤ F := Nat.le_trans hsqm (Nat.le_trans hmF hNF)
  have hWF : W ≤ F := Nat.le_trans hWB (Nat.le_trans hBsq hsqF)
  have hF2 : 2 ≤ F := Nat.le_trans hB2 (Nat.le_trans hBsq hsqF)
  -- (C+1)^m ≤ F^(B²+1)
  have hBm : B ^ m = (B ^ 2) ^ (B ^ 2 + 1) := by
    rw [hm]
    have e2 : 2 * B ^ 2 + 2 = 2 * (B ^ 2 + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [e2, pow_mul_pure B 2 (B ^ 2 + 1)]
  have hCm : (C + 1) ^ m ≤ F ^ (B ^ 2 + 1) :=
    Nat.le_trans (Nat.pow_le_pow_left hCB m)
      (Nat.le_trans (Nat.le_of_eq hBm) (Nat.pow_le_pow_left hsqF (B ^ 2 + 1)))
  -- RHS ≤ F^(1 + (B²+1+D))
  have hRHS : W * ((C + 1) ^ m * F ^ D) ≤ F ^ (1 + (B ^ 2 + 1 + D)) := by
    calc W * ((C + 1) ^ m * F ^ D)
        ≤ F * (F ^ (B ^ 2 + 1) * F ^ D) :=
          Nat.mul_le_mul hWF (Nat.mul_le_mul hCm (Nat.le_refl _))
      _ = F ^ (1 + (B ^ 2 + 1 + D)) := by
          rw [E213.Meta.Nat.PureNat.pow_add F 1 (B ^ 2 + 1 + D), Nat.pow_one,
              ← E213.Meta.Nat.PureNat.pow_add F (B ^ 2 + 1) D]
  -- exponent strictly below N+m
  have hD : D < N + B ^ 2 :=
    Nat.lt_of_le_of_lt hDB (Nat.lt_of_lt_of_le hBltsq (Nat.le_add_left (B ^ 2) N))
  -- two pure add identities
  have eqL : 1 + (B ^ 2 + 1 + D) = B ^ 2 + (D + 2) := by
    calc 1 + (B ^ 2 + 1 + D) = (B ^ 2 + 1 + D) + 1 := Nat.add_comm 1 _
      _ = (B ^ 2 + 1) + (D + 1) := Nat.add_assoc (B ^ 2 + 1) D 1
      _ = B ^ 2 + (1 + (D + 1)) := Nat.add_assoc (B ^ 2) 1 (D + 1)
      _ = B ^ 2 + ((D + 1) + 1) := by rw [Nat.add_comm 1 (D + 1)]
      _ = B ^ 2 + (D + (1 + 1)) := by rw [Nat.add_assoc D 1 1]
  have eqR : B ^ 2 + ((N + B ^ 2) + 2) = N + (2 * B ^ 2 + 2) := by
    rw [E213.Tactic.NatHelper.two_mul]
    calc B ^ 2 + ((N + B ^ 2) + 2)
        = (B ^ 2 + (N + B ^ 2)) + 2 := (Nat.add_assoc (B ^ 2) (N + B ^ 2) 2).symm
      _ = ((N + B ^ 2) + B ^ 2) + 2 := by rw [Nat.add_comm (B ^ 2) (N + B ^ 2)]
      _ = (N + (B ^ 2 + B ^ 2)) + 2 := by rw [Nat.add_assoc N (B ^ 2) (B ^ 2)]
      _ = N + ((B ^ 2 + B ^ 2) + 2) := Nat.add_assoc N (B ^ 2 + B ^ 2) 2
  have hexp : 1 + (B ^ 2 + 1 + D) < N + m := by
    rw [hm, eqL, ← eqR]
    exact Nat.add_lt_add_left (Nat.add_lt_add_right hD 2) (B ^ 2)
  exact Nat.lt_of_le_of_lt hRHS (pow_lt_pow_right_pure hF2 hexp)

/-- ★★★ **`(n!)ⁿ` is genuinely non-holonomic** — it satisfies no polynomial-coefficient
    linear recurrence (refutes the Klazar growth majorant for every order/degree/threshold).
    The first ∅-axiom certificate of *non-holonomicity proper*, strictly above the
    non-Hurwitzian-but-C-finite `2ⁿ` of `HurwitzianCF.geometric_not_quasipoly`. -/
theorem superFact_nonHolonomic : ¬ HolonomicGrowth superFact := by
  rintro ⟨k, C, D, N, hk, hrec⟩
  obtain ⟨m, hlt⟩ := envelope_exceeded (windowSum k superFact N) C D N
  have hb : superFact (N + m) ≤ windowSum k superFact N * env C D N m :=
    holonomicGrowth_value_bound hk hrec m
  exact absurd (Nat.lt_of_le_of_lt hb hlt) (Nat.lt_irrefl _)

end E213.Lib.Math.Cauchy.NonHolonomicWitness
