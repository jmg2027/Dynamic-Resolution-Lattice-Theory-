import E213.Lib.Math.DyadicFSM.PhiMod5
import E213.Lib.Math.DyadicFSM.PellMatrix
/-!
# Pell ↔ Fibonacci bridge (mod p) — G119 Phase 3.2 reduction

The classical identity `U_k = F_{2k}` (where `U_k` is the Pell number
satisfying `U_{k+1} = 3·U_k - U_{k-1}` and `F_n` is the standard
Fibonacci number) reduces the Pell matrix coefficient recurrence
to a fact about Fibonacci numbers at even indices.

For the (1, 1) orbit of `M = [[2, 1], [1, 1]]`:

  `pellCoeff p hp k = (F_{2k} mod p,  (p - F_{2k-2}) mod p)`
                                   (for k ≥ 1; `pellCoeff p hp 0 = (0, 1)`)

So `pellCoeff p hp N = (0, 1)` iff
  `F_{2N} ≡ 0 mod p`  AND  `F_{2N-2} ≡ -1 mod p`.

For Phase 3.2 (split case, `N = (p-1)/2`), this becomes:
  `F_{p-1} ≡ 0 mod p`  AND  `F_{p-3} ≡ -1 mod p`,
which is the classical Fibonacci-Pisano condition at split primes.

This file:
  · Defines `fibFst k := (fibLike k).1` (convenience accessor).
  · Proves `fibFst_recur` (standard Fibonacci recurrence).
  · Proves `fibFst_pell_recur` (the even-index identity
    `F_{2k+4} + F_{2k} = 3·F_{2k+2}` — the Pell recurrence in additive
    Nat form).
  · Smoke-verifies Phase 3.2 fibLike conditions at split primes
    `p ∈ {11, 19, 29}`.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.PellFibBridge

open E213.Lib.Math.DyadicFSM.PhiMod5 (fibLike)
open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeff)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self div_add_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Tactic.NatHelper (add_mul sub_add_cancel add_mul_mod_self_pure)

/-- First component of `fibLike k` — the k-th Fibonacci number. -/
def fibFst (k : Nat) : Nat := (fibLike k).1

/-- Second component of `fibLike k` — `F_{k-1}` for k ≥ 1, and 1 for k=0
    (Fibonacci convention `F_{-1} = 1` extended backward). -/
def fibSnd (k : Nat) : Nat := (fibLike k).2

/-- Definitional: `(fibLike (k+1)).1 = (fibLike k).1 + (fibLike k).2`. -/
theorem fibLike_succ_fst (k : Nat) :
    (fibLike (k + 1)).1 = (fibLike k).1 + (fibLike k).2 := rfl

/-- Definitional: `(fibLike (k+1)).2 = (fibLike k).1`. -/
theorem fibLike_succ_snd (k : Nat) :
    (fibLike (k + 1)).2 = (fibLike k).1 := rfl

/-- ★ **Fibonacci recurrence**: `F_{k+2} = F_{k+1} + F_k`.  PURE. -/
theorem fibFst_recur (k : Nat) :
    fibFst (k + 2) = fibFst (k + 1) + fibFst k := by
  show (fibLike (k + 2)).1 = (fibLike (k + 1)).1 + (fibLike k).1
  rw [fibLike_succ_fst (k + 1), fibLike_succ_snd k]

/-- Smoke: first few Fibonacci values. -/
theorem fibFst_table :
    fibFst 0 = 0 ∧ fibFst 1 = 1 ∧ fibFst 2 = 1 ∧ fibFst 3 = 2
    ∧ fibFst 4 = 3 ∧ fibFst 5 = 5 ∧ fibFst 6 = 8 ∧ fibFst 7 = 13
    ∧ fibFst 8 = 21 ∧ fibFst 9 = 34 ∧ fibFst 10 = 55 := by decide

/-- ★ **Pell-like recurrence on even-index Fibonacci**:
    `F_{2k+4} + F_{2k} = 3·F_{2k+2}` — the Pell recurrence
    in additive Nat form (avoids Nat subtraction).

    Algebraic derivation:
      F_{2k+4}          = F_{2k+3} + F_{2k+2}                [Fibonacci]
                        = (F_{2k+2} + F_{2k+1}) + F_{2k+2}   [Fibonacci]
                        = 2·F_{2k+2} + F_{2k+1}
      F_{2k+4} + F_{2k} = 2·F_{2k+2} + (F_{2k+1} + F_{2k})
                        = 2·F_{2k+2} + F_{2k+2}              [Fibonacci]
                        = 3·F_{2k+2}.
    PURE. -/
theorem fibFst_pell_recur (k : Nat) :
    fibFst (2*k + 4) + fibFst (2*k) = 3 * fibFst (2*k + 2) := by
  have h1 : fibFst (2*k + 4) = fibFst (2*k + 3) + fibFst (2*k + 2) :=
    fibFst_recur (2*k + 2)
  have h2 : fibFst (2*k + 3) = fibFst (2*k + 2) + fibFst (2*k + 1) :=
    fibFst_recur (2*k + 1)
  have h3 : fibFst (2*k + 2) = fibFst (2*k + 1) + fibFst (2*k) :=
    fibFst_recur (2*k)
  rw [h1, h2]
  -- Goal: (F_{2k+2} + F_{2k+1}) + F_{2k+2} + F_{2k} = 3 * F_{2k+2}
  -- Rearrange: (F_{2k+2}) + (F_{2k+2}) + (F_{2k+1} + F_{2k}) = 3 * F_{2k+2}
  rw [Nat.add_assoc (fibFst (2*k + 2) + fibFst (2*k + 1)) (fibFst (2*k + 2)) (fibFst (2*k))]
  -- (F_{2k+2} + F_{2k+1}) + (F_{2k+2} + F_{2k}) = 3 * F_{2k+2}
  rw [Nat.add_assoc (fibFst (2*k + 2)) (fibFst (2*k + 1)) (fibFst (2*k + 2) + fibFst (2*k))]
  -- F_{2k+2} + (F_{2k+1} + (F_{2k+2} + F_{2k})) = 3 * F_{2k+2}
  rw [show fibFst (2*k + 1) + (fibFst (2*k + 2) + fibFst (2*k))
        = fibFst (2*k + 2) + (fibFst (2*k + 1) + fibFst (2*k)) by
      rw [← Nat.add_assoc, Nat.add_comm (fibFst (2*k + 1)) (fibFst (2*k + 2)),
          Nat.add_assoc]]
  -- F_{2k+2} + (F_{2k+2} + (F_{2k+1} + F_{2k})) = 3 * F_{2k+2}
  rw [← h3]
  -- F_{2k+2} + (F_{2k+2} + F_{2k+2}) = 3 * F_{2k+2}
  show fibFst (2*k + 2) + (fibFst (2*k + 2) + fibFst (2*k + 2)) = 3 * fibFst (2*k + 2)
  rw [show 3 * fibFst (2*k + 2) = fibFst (2*k + 2) + fibFst (2*k + 2) + fibFst (2*k + 2) by
        rw [show (3 : Nat) = 1 + 1 + 1 from rfl, add_mul, add_mul,
            Nat.one_mul]]
  rw [Nat.add_assoc]

/-! ## Phase 3.2 fibLike conditions — per-prime smokes

At split primes p (5 QR mod p), the Phase 3.2 chain requires:

  `F_{p-1} ≡ 0 (mod p)`  AND  `F_{p-3} ≡ -1 (mod p)`

The universal claim follows from FLT for phi (multi-session); each
per-prime instance is decidable.  The smokes below verify the
condition at the 11 empirically-tight split primes from the G119
Predictor23 chain. -/

/-- Smoke at p=11 (split, predict (11-1)/2 = 5):
    F_10 ≡ 0 mod 11 AND F_8 ≡ -1 mod 11. -/
theorem fib_phase_3_2_at_11 :
    fibFst 10 % 11 = 0 ∧ fibFst 8 % 11 = 10 := by decide

/-- Smoke at p=19 (split, predict 9):
    F_18 ≡ 0 mod 19 AND F_16 ≡ -1 mod 19. -/
theorem fib_phase_3_2_at_19 :
    fibFst 18 % 19 = 0 ∧ fibFst 16 % 19 = 18 := by decide

/-- Smoke at p=29 (split, predict 14):
    F_28 ≡ 0 mod 29 AND F_26 ≡ -1 mod 29.
    Note: p=29 is sub-tight (actual period 7 < predict 14), but the
    predict upper-bound still holds. -/
theorem fib_phase_3_2_at_29 :
    fibFst 28 % 29 = 0 ∧ fibFst 26 % 29 = 28 := by decide

/-- Smoke at p=31 (split, predict 15):
    F_30 ≡ 0 mod 31 AND F_28 ≡ -1 mod 31. -/
theorem fib_phase_3_2_at_31 :
    fibFst 30 % 31 = 0 ∧ fibFst 28 % 31 = 30 := by decide

/-- Smoke at p=41 (split, predict 20):
    F_40 ≡ 0 mod 41 AND F_38 ≡ -1 mod 41. -/
theorem fib_phase_3_2_at_41 :
    fibFst 40 % 41 = 0 ∧ fibFst 38 % 41 = 40 := by decide

/-! ## Mod-cancellation helper toward the Pell-Fib bridge proper

The full bridge `(pellCoeff p hp k).1.val = fibFst (2k) % p` needs
a coupled induction on pellCoeff's two components.  The inductive
step rewrites

  `(3·(A % p) + (p - B % p) % p) % p   =   C % p`

where `A = fibFst (2k+2)`, `B = fibFst (2k)`, `C = fibFst (2k+4)`,
and `C + B = 3·A` (the Pell recurrence on F).

The hard sub-step is collapsing `(p - B%p)` as `(B/p + 1)·p - B`,
i.e., `B + (p - B%p)` is a multiple of `p`.  The lemma below
captures exactly this.
-/

open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (add_mul sub_add_cancel)

/-- ★ `B + (p - B % p) = (B / p + 1) · p`, for `0 < p`.

    The expression `B + (p - B%p)` is always a multiple of `p` —
    the smallest one `≥ B + 1` when `B % p > 0`, or `B + p` when
    `B % p = 0`.  PURE.

    Derivation:
      `B = p · (B/p) + B%p`            (div_add_mod)
      `B + (p - B%p) = p·(B/p) + B%p + (p - B%p)`
                    = `p·(B/p) + p`     (B%p + (p - B%p) = p)
                    = `(B/p + 1) · p`. -/
theorem add_p_sub_mod (p B : Nat) (hp : 0 < p) :
    B + (p - B % p) = (B / p + 1) * p := by
  have hle : B % p ≤ p := Nat.le_of_lt (Nat.mod_lt B hp)
  have hsac : (p - B % p) + B % p = p := sub_add_cancel hle
  have hdiv : p * (B / p) + B % p = B := div_add_mod B p
  -- Build the equation by `congrArg` chain to avoid `rw` recursion
  -- through `B / p` and `B % p` (both contain `B` as a subterm).
  have e1 : B + (p - B % p) = (p * (B / p) + B % p) + (p - B % p) :=
    congrArg (· + (p - B % p)) hdiv.symm
  have e2 : (p * (B / p) + B % p) + (p - B % p)
          = p * (B / p) + (B % p + (p - B % p)) :=
    Nat.add_assoc _ _ _
  have e3 : B % p + (p - B % p) = p := by
    rw [Nat.add_comm]; exact hsac
  have e4 : p * (B / p) + (B % p + (p - B % p)) = p * (B / p) + p :=
    congrArg (p * (B / p) + ·) e3
  have e5 : p * (B / p) + p = (B / p + 1) * p := by
    rw [Nat.mul_comm p (B / p)]
    rw [show (B / p + 1) * p = B / p * p + 1 * p from add_mul _ _ _,
        Nat.one_mul]
  exact e1.trans (e2.trans (e4.trans e5))

/-- ★ **First-component bridge step**: the modular cancellation that
    closes the inductive step `(pellCoeff (k+1)).1.val = F_{2k+2} mod p`.

    `(3 · (A % p) + (p - B % p) % p) % p = C % p`,
    given `C + B = 3·A` (Pell-Fib recurrence) and `p > 0`.

    PURE.  Uses `add_p_sub_mod` to absorb the `(p - B%p)` into a
    multiple of `p`, then `add_mul_mod_self_pure` to cancel. -/
theorem first_step (p A B C : Nat) (hp : 0 < p)
    (hPell : C + B = 3 * A) :
    (3 * (A % p) + (p - B % p) % p) % p = C % p := by
  rw [add_mod_gen (3 * (A % p)) ((p - B % p) % p) p,
      mod_mod (p - B % p) p,
      ← mul_mod_right_pure 3 A p,
      ← add_mod_gen (3 * A) (p - B % p) p,
      ← hPell,
      Nat.add_assoc,
      add_p_sub_mod p B hp]
  exact add_mul_mod_self_pure C p (B / p + 1)

/-- ★★★★ **Pell-Fibonacci coupled bridge** (G119 Phase 3.2 reduction):

    For all `k ≥ 1`, `pellCoeff p hp k` is exactly the Pell-coefficient
    pair derived from even-indexed Fibonacci numbers mod p:

      `(pellCoeff p hp (k+1)).1.val = F_{2k+2} mod p`
      `(pellCoeff p hp (k+1)).2.val = (p - F_{2k} mod p) mod p`

    Coupled induction on `k`:
      · base: pellCoeff 1 = (1, 0) matches (F_2 mod p, (p - F_0 mod p) mod p)
        = (1 mod p, (p - 0) mod p) = (1, 0) for p > 1.
      · step: pellCoeff (k+2) = step(pellCoeff (k+1)).
        First component: `(3a + b) % p = (3·F_{2k+2}·-F_{2k}) mod p
        = F_{2k+4} mod p` via `first_step` + Pell-Fib recurrence.
        Second component: `(p - a) % p = (p - F_{2k+2}) mod p` directly.

    PURE.  This reduces Phase 3.2 to the Fibonacci-Pisano condition
    `F_{p-1} ≡ 0 ∧ F_{p-3} ≡ -1 (mod p)` at split primes. -/
theorem pellCoeff_eq_fib_bridge (p : Nat) (hp : 1 < p) :
    ∀ k, (pellCoeff p hp (k + 1)).1.val = fibFst (2 * k + 2) % p
       ∧ (pellCoeff p hp (k + 1)).2.val = (p - fibFst (2 * k) % p) % p
  | 0 => by
    -- pellCoeff p hp 1 = (⟨1 % p, _⟩, ⟨(p - 0) % p, _⟩) by computation,
    -- which matches (F_2 % p, (p - F_0 % p) % p) = (1 % p, (p - 0) % p) by rfl.
    refine ⟨?_, ?_⟩ <;> rfl
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := pellCoeff_eq_fib_bridge p hp k
    have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
    refine ⟨?_, ?_⟩
    · -- First component: pellCoeff (k+2) .1 = F_{2(k+1)+2} % p = F_{2k+4} % p
      show (3 * (pellCoeff p hp (k+1)).1.val
              + (pellCoeff p hp (k+1)).2.val) % p
         = fibFst (2 * (k + 1) + 2) % p
      rw [ih1, ih2]
      -- Goal:  (3 * (F_{2k+2} % p) + (p - F_{2k} % p) % p) % p
      --      = F_{2*(k+1)+2} % p
      -- Note 2 * (k+1) + 2 = 2*k + 4 by Nat algebra.
      show (3 * (fibFst (2 * k + 2) % p) + (p - fibFst (2 * k) % p) % p) % p
         = fibFst (2 * k + 4) % p
      exact first_step p (fibFst (2*k+2)) (fibFst (2*k)) (fibFst (2*k+4))
        hp_pos (fibFst_pell_recur k)
    · -- Second component: pellCoeff (k+2) .2 = (p - F_{2(k+1)} % p) % p
      --                                      = (p - F_{2k+2} % p) % p
      show (p - (pellCoeff p hp (k+1)).1.val % p) % p
         = (p - fibFst (2 * (k + 1)) % p) % p
      rw [ih1, mod_mod (fibFst (2 * k + 2)) p]
      -- Goal:  (p - F_{2k+2} % p) % p  =  (p - F_{2(k+1)} % p) % p
      -- 2 * (k+1) = 2*k + 2 by defeq.
      rfl

open E213.Tactic.NatHelper (sub_sub_self)

/-- ★★★★★ **Conditional Phase 3.2 closure** for an arbitrary index `N' + 1`:

    given Fibonacci-Pisano conditions
      · `fibFst (2·N' + 2) % p = 0`         (i.e., `F_{2N'+2} ≡ 0 mod p`)
      · `fibFst (2·N') % p = p - 1`         (i.e., `F_{2N'} ≡ -1 mod p`)
    the matrix `M^(N'+1) = I` mod p, equivalently
      `pellCoeff p hp (N' + 1) = pellCoeff p hp 0 = (⟨0, _⟩, ⟨1, _⟩)`.

    For Phase 3.2 specifically at split primes with `N' + 1 = (p-1)/2`
    (so `2·N' + 2 = p - 1` and `2·N' = p - 3`), this reduces matrix-order
    closure to the **Fibonacci-Pisano condition**:
      `F_{p-1} ≡ 0 mod p  ∧  F_{p-3} ≡ -1 mod p`.
    The latter is classical FLT-equivalent for split primes (multi-session).

    PURE.  Combines the `pellCoeff_eq_fib_bridge` (this file) with
    Nat algebra. -/
theorem phase_3_2_closure (p : Nat) (hp : 1 < p) (N' : Nat)
    (h_F : fibFst (2 * N' + 2) % p = 0)
    (h_F_minus_1 : fibFst (2 * N') % p = p - 1) :
    pellCoeff p hp (N' + 1) = pellCoeff p hp 0 := by
  obtain ⟨h1, h2⟩ := pellCoeff_eq_fib_bridge p hp N'
  -- pellCoeff p hp 0 = (⟨0, _⟩, ⟨1, _⟩) by definition
  -- Want: pellCoeff p hp (N'+1) = (⟨0, _⟩, ⟨1, _⟩)
  -- Show via Prod.ext + Fin.ext on .val components
  have hone_le_p : 1 ≤ p := Nat.le_of_lt hp
  apply Prod.ext
  · apply Fin.ext
    show (pellCoeff p hp (N' + 1)).1.val = 0
    rw [h1, h_F]
  · apply Fin.ext
    show (pellCoeff p hp (N' + 1)).2.val = 1
    rw [h2, h_F_minus_1]
    -- Goal: (p - (p - 1)) % p = 1
    rw [sub_sub_self hone_le_p]
    -- Goal: 1 % p = 1
    exact Nat.mod_eq_of_lt hp

/-! ## Per-prime Phase 3.2 closure (split primes) -/

/-- Phase 3.2 at p=11: `pellCoeff 11 _ 5 = pellCoeff 11 _ 0 = (0, 1)`.
    Derived from `phase_3_2_closure` + per-prime fibLike smokes
    (`fib_phase_3_2_at_11`).  PURE.

    Note: N' = 4, so N' + 1 = 5 = (p-1)/2 for p=11. -/
theorem pellCoeff_11_5_eq_init_via_bridge :
    pellCoeff 11 (by decide) 5 = pellCoeff 11 (by decide) 0 :=
  phase_3_2_closure 11 (by decide) 4
    fib_phase_3_2_at_11.1 fib_phase_3_2_at_11.2

/-- Phase 3.2 at p=19: `pellCoeff 19 _ 9 = pellCoeff 19 _ 0`. -/
theorem pellCoeff_19_9_eq_init_via_bridge :
    pellCoeff 19 (by decide) 9 = pellCoeff 19 (by decide) 0 :=
  phase_3_2_closure 19 (by decide) 8
    fib_phase_3_2_at_19.1 fib_phase_3_2_at_19.2

/-- Phase 3.2 at p=29 (sub-tight, predict=14): `pellCoeff 29 _ 14 = (0, 1)`. -/
theorem pellCoeff_29_14_eq_init_via_bridge :
    pellCoeff 29 (by decide) 14 = pellCoeff 29 (by decide) 0 :=
  phase_3_2_closure 29 (by decide) 13
    fib_phase_3_2_at_29.1 fib_phase_3_2_at_29.2

/-- Phase 3.2 at p=31 (split, predict=15). -/
theorem pellCoeff_31_15_eq_init_via_bridge :
    pellCoeff 31 (by decide) 15 = pellCoeff 31 (by decide) 0 :=
  phase_3_2_closure 31 (by decide) 14
    fib_phase_3_2_at_31.1 fib_phase_3_2_at_31.2

/-- Phase 3.2 at p=41 (split, predict=20). -/
theorem pellCoeff_41_20_eq_init_via_bridge :
    pellCoeff 41 (by decide) 20 = pellCoeff 41 (by decide) 0 :=
  phase_3_2_closure 41 (by decide) 19
    fib_phase_3_2_at_41.1 fib_phase_3_2_at_41.2

/-! ## Extended split primes: 59, 61, 71, 79, 89, 101 -/

/-- Smoke at p=59 (split, predict 29). -/
theorem fib_phase_3_2_at_59 :
    fibFst 58 % 59 = 0 ∧ fibFst 56 % 59 = 58 := by decide

theorem pellCoeff_59_29_eq_init_via_bridge :
    pellCoeff 59 (by decide) 29 = pellCoeff 59 (by decide) 0 :=
  phase_3_2_closure 59 (by decide) 28
    fib_phase_3_2_at_59.1 fib_phase_3_2_at_59.2

/-- Smoke at p=61 (split, predict 30). -/
theorem fib_phase_3_2_at_61 :
    fibFst 60 % 61 = 0 ∧ fibFst 58 % 61 = 60 := by decide

theorem pellCoeff_61_30_eq_init_via_bridge :
    pellCoeff 61 (by decide) 30 = pellCoeff 61 (by decide) 0 :=
  phase_3_2_closure 61 (by decide) 29
    fib_phase_3_2_at_61.1 fib_phase_3_2_at_61.2

/-- Smoke at p=71 (split, predict 35). -/
theorem fib_phase_3_2_at_71 :
    fibFst 70 % 71 = 0 ∧ fibFst 68 % 71 = 70 := by decide

theorem pellCoeff_71_35_eq_init_via_bridge :
    pellCoeff 71 (by decide) 35 = pellCoeff 71 (by decide) 0 :=
  phase_3_2_closure 71 (by decide) 34
    fib_phase_3_2_at_71.1 fib_phase_3_2_at_71.2

/-- Smoke at p=79 (split, predict 39). -/
theorem fib_phase_3_2_at_79 :
    fibFst 78 % 79 = 0 ∧ fibFst 76 % 79 = 78 := by decide

theorem pellCoeff_79_39_eq_init_via_bridge :
    pellCoeff 79 (by decide) 39 = pellCoeff 79 (by decide) 0 :=
  phase_3_2_closure 79 (by decide) 38
    fib_phase_3_2_at_79.1 fib_phase_3_2_at_79.2

/-- Smoke at p=89 (split, sub-tight predict 44). -/
theorem fib_phase_3_2_at_89 :
    fibFst 88 % 89 = 0 ∧ fibFst 86 % 89 = 88 := by decide

theorem pellCoeff_89_44_eq_init_via_bridge :
    pellCoeff 89 (by decide) 44 = pellCoeff 89 (by decide) 0 :=
  phase_3_2_closure 89 (by decide) 43
    fib_phase_3_2_at_89.1 fib_phase_3_2_at_89.2

/-- Smoke at p=101 (split, sub-tight predict 50). -/
theorem fib_phase_3_2_at_101 :
    fibFst 100 % 101 = 0 ∧ fibFst 98 % 101 = 100 := by decide

theorem pellCoeff_101_50_eq_init_via_bridge :
    pellCoeff 101 (by decide) 50 = pellCoeff 101 (by decide) 0 :=
  phase_3_2_closure 101 (by decide) 49
    fib_phase_3_2_at_101.1 fib_phase_3_2_at_101.2

end E213.Lib.Math.DyadicFSM.PellFibBridge
