import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Norm
import E213.Lib.Math.ModArith.UniversalFLT
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
/-!
# Real213-p-adic — natural-number power

`Zp.pow x n` is defined recursively via `Zp.mul`:
- `Zp.pow x 0 = ZpSeq.one`
- `Zp.pow x (n+1) = Zp.mul (Zp.pow x n) x`

The key compatibility theorem is `Zp.pow_trunc`:
`(Zp.pow x n).trunc m = (x.trunc m)^n % p^m`,
expressing trunc as a ring homomorphism from `ZpSeq` to `ℤ/p^m`.

This is foundational for Teichmüller lifts and other multiplicative
structures on `ℤ_p`.
-/

namespace E213.Lib.Math.Padic

/-- Natural-number power on `ZpSeq`.  Defined recursively as
    repeated multiplication. -/
def Zp.pow (p : Nat) (hp : 1 < p) (x : ZpSeq p) : Nat → ZpSeq p
  | 0 => ZpSeq.one p hp
  | n + 1 => Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) x

/-- `Zp.pow x 0 = 1`. -/
theorem Zp.pow_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    Zp.pow p hp x 0 = ZpSeq.one p hp := rfl

/-- `Zp.pow x (n + 1) = Zp.pow x n · x`. -/
theorem Zp.pow_succ_def (p : Nat) (hp : 1 < p) (x : ZpSeq p) (n : Nat) :
    Zp.pow p hp x (n + 1)
      = Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) x := rfl

/-! ## Trunc compatibility -/

/-- `(ZpSeq.one).trunc m = 1 % p^m` — at m = 0 it's 0, otherwise 1. -/
private theorem one_trunc_form (p : Nat) (hp : 1 < p) :
    ∀ m, (ZpSeq.one p hp).trunc m = 1 % p^m
  | 0 => by
    show (0 : Nat) = 1 % p^0
    rw [Nat.pow_zero]
  | m + 1 => by
    rw [ZpSeq.trunc_one_succ p hp m]
    have h_lt : 1 < p^(m + 1) := by
      induction m with
      | zero => rw [Nat.pow_one]; exact hp
      | succ k ih =>
        have hp' : 0 < p := Nat.lt_of_succ_lt hp
        calc 1 < p^(k + 1) := ih
          _ ≤ p^(k + 1) * p := Nat.le_mul_of_pos_right _ hp'
          _ = p^(k + 2) := (Nat.pow_succ p (k + 1)).symm
    exact (Nat.mod_eq_of_lt h_lt).symm

/-- **Trunc compatibility**: `(Zp.pow x n).trunc m = (x.trunc m)^n % p^m`.
    Proved by induction on `n`. -/
theorem Zp.pow_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (m : Nat) :
    ∀ n, (Zp.pow p hp x n).trunc m = (x.trunc m)^n % p^m
  | 0 => by
    show (ZpSeq.one p hp).trunc m = (x.trunc m)^0 % p^m
    rw [one_trunc_form p hp m, Nat.pow_zero]
  | n + 1 => by
    rw [Zp.pow_succ_def]
    rw [Zp.mul_trunc p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) x m]
    rw [Zp.pow_trunc p hp x m n]
    -- LHS: ((x.trunc m)^n % p^m * x.trunc m) % p^m
    -- RHS: (x.trunc m)^(n+1) % p^m
    rw [← E213.Meta.Nat.MulMod213.mul_mod_left_pure
          ((x.trunc m)^n) (x.trunc m) (p^m)]
    -- LHS: ((x.trunc m)^n * x.trunc m) % p^m
    rw [Nat.pow_succ (x.trunc m) n]

/-! ## Useful identities -/

/-- PURE: `a^m * a^n = a^(m+n)` by induction. -/
private theorem pow_add_pure_local (a : Nat) :
    ∀ m n, a^m * a^n = a^(m + n)
  | _, 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | m, n + 1 => by
    rw [Nat.pow_succ, ← E213.Tactic.NatHelper.mul_assoc,
        pow_add_pure_local a m n]
    show a^(m + n) * a = a^(m + (n + 1))
    rw [← Nat.add_assoc, ← Nat.pow_succ]

/-- `Zp.pow x 2 = Zp.mul (Zp.mul one x) x`.  Note this isn't `Zp.mul x x`
    directly because `pow` does `pow 0 = one`, then `pow 1 = one · x`,
    then `pow 2 = (one · x) · x`. -/
theorem Zp.pow_two_def (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    Zp.pow p hp x 2
      = Zp.mul p (Nat.lt_of_succ_lt hp)
          (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x) x := rfl

/-- `(Zp.pow x 2).trunc m = (x.trunc m)² % p^m`. -/
theorem Zp.pow_two_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (m : Nat) :
    (Zp.pow p hp x 2).trunc m = (x.trunc m * x.trunc m) % p^m := by
  rw [Zp.pow_trunc p hp x m 2]
  show (x.trunc m)^2 % p^m = (x.trunc m * x.trunc m) % p^m
  rw [show (x.trunc m)^2 = x.trunc m * x.trunc m by
        rw [Nat.pow_succ, Nat.pow_one]]

/-- **Multiplicative homomorphism at trunc**:
    `(Zp.pow x (m + n)).trunc k = (Zp.pow x m · Zp.pow x n).trunc k`. -/
theorem Zp.pow_add_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (k m n : Nat) :
    (Zp.pow p hp x (m + n)).trunc k
      = (Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x m) (Zp.pow p hp x n)).trunc k := by
  rw [Zp.mul_trunc p (Nat.lt_of_succ_lt hp) _ _ k]
  rw [Zp.pow_trunc p hp x k (m + n), Zp.pow_trunc p hp x k m,
      Zp.pow_trunc p hp x k n]
  -- Goal: (x.trunc k)^(m+n) % p^k = ((x.trunc k)^m % p^k * ((x.trunc k)^n % p^k)) % p^k
  rw [← pow_add_pure_local (x.trunc k) m n]
  -- Goal: ((x.trunc k)^m * (x.trunc k)^n) % p^k
  --     = ((x.trunc k)^m % p^k * ((x.trunc k)^n % p^k)) % p^k
  exact E213.Meta.Nat.MulMod213.mul_mod_pure _ _ _

/-- PURE: `a^p = a^(p - 1) * a` for `0 < p`. -/
private theorem pow_pred_eq (a p : Nat) (hp : 0 < p) :
    a^p = a^(p - 1) * a := by
  cases p with
  | zero => exact absurd hp (Nat.lt_irrefl 0)
  | succ k =>
    show a^(k + 1) = a^(k + 1 - 1) * a
    rw [show k + 1 - 1 = k from rfl]
    exact Nat.pow_succ a k

/-! ## Fermat's little theorem on `ZpSeq`

For p prime, `x^p ≡ x (mod p)` for any `x : ZpSeq p`.  This is the
first-digit case of the Teichmüller convergence: iterating `x ↦ x^p`
fixes the digit-0 mod p.
-/

/-- **Fermat's lift to digit-0**: for `p` prime (encoded as
    `prime_gcd p`), `(Zp.pow x p).trunc 1 = x.trunc 1`.

    Proof: `(x^p).trunc 1 = (x.trunc 1)^p % p`.  By Fermat
    (`universal_flt_main`), `a^(p-1) ≡ 1 (mod p)`, so `a^p ≡ a (mod p)`.
    Since `x.trunc 1 < p`, the mod is trivial. -/
theorem Zp.pow_p_trunc_one (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m
                  → m < p
                  → (E213.Lib.Math.ModArith.ModBezout.modBezout m p).1 = 1) :
    (Zp.pow p hp x p).trunc 1 = x.trunc 1 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  rw [Zp.pow_trunc p hp x 1 p, Nat.pow_one]
  -- Goal: (x.trunc 1)^p % p = x.trunc 1
  -- x.trunc 1 < p^1 = p.
  have h_lt : x.trunc 1 < p := by
    have h := ZpSeq.trunc_lt_p_pow hp' x 1
    rw [Nat.pow_one] at h
    exact h
  -- Case on whether x.trunc 1 = 0.
  cases h_case : Nat.decEq (x.trunc 1) 0 with
  | isTrue h_zero =>
    rw [h_zero]
    -- 0^p % p = 0.  p > 0 so p ≥ 1, so 0^p = 0 when p ≥ 1.  For p = 1
    -- (excluded by 1 < p), 0^0 = 1.  Here p > 1 so p ≥ 2, 0^p = 0.
    have : (0 : Nat)^p = 0 := by
      cases p with
      | zero => exact absurd hp (Nat.not_lt_zero 1)
      | succ q => show (0 : Nat)^(q + 1) = 0; rw [Nat.pow_succ, Nat.mul_zero]
    rw [this, E213.Tactic.NatHelper.zero_mod]
  | isFalse h_ne =>
    have h_pos : 0 < x.trunc 1 := Nat.pos_of_ne_zero h_ne
    rw [pow_pred_eq (x.trunc 1) p hp']
    -- Goal: ((x.trunc 1)^(p-1) * x.trunc 1) % p = x.trunc 1
    -- Apply mul_mod_left_pure to reduce the first factor mod p.
    rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure
          ((x.trunc 1)^(p - 1)) (x.trunc 1) p]
    -- Goal: (((x.trunc 1)^(p-1) % p) * x.trunc 1) % p = x.trunc 1
    rw [E213.Lib.Math.ModArith.UniversalFLT.universal_flt_main
          (x.trunc 1) p hp h_pos h_lt h_prime_gcd]
    -- Goal: ((1 % p) * x.trunc 1) % p = x.trunc 1
    rw [Nat.mod_eq_of_lt hp, Nat.one_mul]
    exact Nat.mod_eq_of_lt h_lt

/-- Smoke: `2^5 ≡ 2 (mod 5)` in `ℤ_5`.  Build an `x` with digit-0 = 2
    and verify Fermat at the digit level. -/
theorem Zp.smoke_pow_5_digit_two :
    (Zp.pow 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩ 5).trunc 1
      = 2 := by
  rw [Zp.pow_p_trunc_one 5 (by decide) _
        E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_5]
  -- (x.trunc 1) where x.digits 0 = 2.
  rfl

/-! ## Teichmüller iteration

The map `x ↦ x^p` iterated `n` times gives `x^(p^n)`.  In the
classical Teichmüller theory, this sequence converges in ℤ_p
(for d coprime to p) to the unique `(p-1)`-th root of unity ≡ d.

We define the iteration and prove the digit-0 invariant.  The
full convergence statement is deeper and deferred.
-/

/-- Teichmüller iteration: `iter x n = x^(p^n)` formally.
    Each step raises to the p-th power. -/
def Zp.teichmuller_iter (p : Nat) (hp : 1 < p) (x : ZpSeq p) : Nat → ZpSeq p
  | 0 => x
  | n + 1 => Zp.pow p hp (Zp.teichmuller_iter p hp x n) p

/-- Level 0 is `x` itself. -/
theorem Zp.teichmuller_iter_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    Zp.teichmuller_iter p hp x 0 = x := rfl

/-- Successor step: `iter x (n + 1) = (iter x n)^p`. -/
theorem Zp.teichmuller_iter_succ (p : Nat) (hp : 1 < p) (x : ZpSeq p) (n : Nat) :
    Zp.teichmuller_iter p hp x (n + 1)
      = Zp.pow p hp (Zp.teichmuller_iter p hp x n) p := rfl

/-- **Digit-0 invariant**: for `p` prime, every Teichmüller iterate
    has the same trunc-1 (i.e., the same digit 0 mod p).

    `(teichmuller_iter x n).trunc 1 = x.trunc 1` for all `n`. -/
theorem Zp.teichmuller_iter_trunc_one (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m
                  → m < p
                  → (E213.Lib.Math.ModArith.ModBezout.modBezout m p).1 = 1) :
    ∀ n, (Zp.teichmuller_iter p hp x n).trunc 1 = x.trunc 1
  | 0 => rfl
  | n + 1 => by
    rw [Zp.teichmuller_iter_succ]
    rw [Zp.pow_p_trunc_one p hp (Zp.teichmuller_iter p hp x n) h_prime_gcd]
    exact Zp.teichmuller_iter_trunc_one p hp x h_prime_gcd n

/-- Smoke: 5-adic Teichmüller iteration starting from digit-0 = 2,
    after 3 iterations the digit 0 is still 2. -/
theorem Zp.smoke_teichmuller_5_iter_3 :
    (Zp.teichmuller_iter 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩ 3).trunc 1
      = 2 := by
  rw [Zp.teichmuller_iter_trunc_one 5 (by decide) _
        E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_5]
  rfl

/-- **Fermat at trunc-1**: for `p` prime and `x` with nonzero digit 0,
    `(Zp.pow x (p - 1)).trunc 1 = 1`.

    Classical Fermat's little theorem lifted to the digit level:
    `x^(p-1) ≡ 1 (mod p)` whenever `x` is a unit mod p.  This is
    the multiplicative order condition that gives ℤ_p contains the
    `(p-1)`-th roots of unity (the Teichmüller representatives). -/
theorem Zp.pow_p_minus_one_trunc_one (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_nz : 0 < (x.digits 0).val)
    (h_prime_gcd : ∀ m, 0 < m
                  → m < p
                  → (E213.Lib.Math.ModArith.ModBezout.modBezout m p).1 = 1) :
    (Zp.pow p hp x (p - 1)).trunc 1 = 1 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  rw [Zp.pow_trunc p hp x 1 (p - 1), Nat.pow_one]
  -- Goal: (x.trunc 1)^(p-1) % p = 1
  -- x.trunc 1 = (x.digits 0).val (by definition).
  have h_trunc1 : x.trunc 1 = (x.digits 0).val := by
    show 0 + (x.digits 0).val * p^0 = (x.digits 0).val
    rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  rw [h_trunc1]
  -- Goal: ((x.digits 0).val)^(p-1) % p = 1
  have h_lt : (x.digits 0).val < p := (x.digits 0).isLt
  have := E213.Lib.Math.ModArith.UniversalFLT.universal_flt_main
            (x.digits 0).val p hp h_nz h_lt h_prime_gcd
  -- this : (x.digits 0).val ^ (p - 1) % p = 1 % p
  rw [this, Nat.mod_eq_of_lt hp]

/-- Smoke: `2^4 ≡ 1 (mod 5)` lifted to `Zp.pow` on a 5-adic with
    digit-0 = 2.  Confirms Fermat at the trunc level. -/
theorem Zp.smoke_pow_4_eq_one_5 :
    (Zp.pow 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩ 4).trunc 1
      = 1 := by
  exact Zp.pow_p_minus_one_trunc_one 5 (by decide) _ (by decide)
    E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_5

/-! ## Multiplicative homomorphism

`(x · y)^n` and `x^n · y^n` agree at the trunc level.  This makes
`Zp.pow x n` a multiplicative homomorphism `ZpSeq → ZpSeq` modulo
truncation.
-/

/-- PURE: `(a * b)^n = a^n * b^n` by induction. -/
private theorem mul_pow_pure (a b : Nat) :
    ∀ n, (a * b)^n = a^n * b^n
  | 0 => by rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.pow_succ, mul_pow_pure a b n, Nat.pow_succ a n, Nat.pow_succ b n]
    show a^n * b^n * (a * b) = a^n * a * (b^n * b)
    rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213 (a^n) (b^n) a b]

/-- PURE: `(a % m)^n % m = a^n % m`.  Mod is invariant under
    pre-reduction in the base. -/
private theorem pow_mod_pure (a m : Nat) :
    ∀ n, ((a % m)^n) % m = a^n % m
  | 0 => by rw [Nat.pow_zero, Nat.pow_zero]
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ]
    -- ((a % m)^n * (a % m)) % m = (a^n * a) % m
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure ((a % m)^n) (a % m) m,
        pow_mod_pure a m n,
        E213.Tactic.NatHelper.mod_mod_pure,
        ← E213.Meta.Nat.MulMod213.mul_mod_pure (a^n) a m]

/-- **Multiplicative homomorphism on the factor side**: at the trunc
    level, `(Zp.pow (x · y) n) = (Zp.pow x n · Zp.pow y n)`. -/
theorem Zp.pow_mul_trunc (p : Nat) (hp : 1 < p) (x y : ZpSeq p) (k n : Nat) :
    (Zp.pow p hp
      (Zp.mul p (Nat.lt_of_succ_lt hp) x y) n).trunc k
      = (Zp.mul p (Nat.lt_of_succ_lt hp)
          (Zp.pow p hp x n) (Zp.pow p hp y n)).trunc k := by
  -- LHS = ((x · y).trunc k)^n % p^k = ((x.trunc k · y.trunc k) % p^k)^n % p^k
  -- RHS = ((x^n).trunc k · (y^n).trunc k) % p^k
  --     = ((x.trunc k)^n % p^k · (y.trunc k)^n % p^k) % p^k
  rw [Zp.pow_trunc p hp _ k n,
      Zp.mul_trunc p (Nat.lt_of_succ_lt hp) x y k]
  rw [Zp.mul_trunc p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) (Zp.pow p hp y n) k,
      Zp.pow_trunc p hp x k n, Zp.pow_trunc p hp y k n]
  -- Goal: ((x.trunc k * y.trunc k) % p^k)^n % p^k
  --     = ((x.trunc k)^n % p^k * ((y.trunc k)^n % p^k)) % p^k
  -- Strip outer % p^k on LHS via pow + mod (need lemma `(a % m)^n % m = a^n % m`).
  rw [pow_mod_pure (x.trunc k * y.trunc k) (p^k) n]
  -- ((x.trunc k * y.trunc k)^n) % p^k = ...
  rw [mul_pow_pure (x.trunc k) (y.trunc k) n]
  -- ((x.trunc k)^n * (y.trunc k)^n) % p^k = ((x.trunc k)^n % p^k * ...) % p^k
  exact E213.Meta.Nat.MulMod213.mul_mod_pure _ _ _

/-! ## Power and valuation

`pow` scales the p-adic valuation: `val(x^k) = k · val(x)` (at trunc).
The valAtLeast form: `valAtLeast x m → valAtLeast (x^k) (m·k)`.
-/

/-- **Power scales valuation**: if `x` has valuation ≥ m, then `x^k`
    has valuation ≥ m·k. -/
theorem Zp.valAtLeast_pow (p : Nat) (hp : 1 < p) (x : ZpSeq p) (m : Nat)
    (hx : Zp.valAtLeast x m) :
    ∀ k, Zp.valAtLeast (Zp.pow p hp x k) (m * k)
  | 0 => by
    rw [Nat.mul_zero]
    exact Zp.valAtLeast_zero _
  | k + 1 => by
    have hp' : 0 < p := Nat.lt_of_succ_lt hp
    have ih : Zp.valAtLeast (Zp.pow p hp x k) (m * k) :=
      Zp.valAtLeast_pow p hp x m hx k
    rw [Zp.pow_succ_def]
    rw [show m * (k + 1) = m * k + m by
          rw [Nat.mul_add, Nat.mul_one]]
    exact Zp.valAtLeast_mul p hp' _ _ (m * k) m ih hx

end E213.Lib.Math.Padic
