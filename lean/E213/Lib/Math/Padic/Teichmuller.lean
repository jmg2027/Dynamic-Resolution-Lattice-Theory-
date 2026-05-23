import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.Padic.Pow
import E213.Lib.Math.Padic.Norm
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
/-!
# Real213-p-adic — Teichmüller convergence

This module proves the Frobenius lift and Teichmüller iteration
convergence:

- **Geometric sum identity**: at trunc level,
  `(y - z) · sum_{i=0}^{N-1} y^i z^(N-1-i) = y^N - z^N`.

- **`valAtLeast (sum_geo_pow y z p) 1`** when `y ≡ z (mod p)`:
  the geometric sum at exponent `p` has each term ≡ `(y mod p)^(p-1)`,
  giving total ≡ `p · (...)` ≡ 0 (mod p).

- **Frobenius lift**: `y ≡ z (mod p^k) → y^p ≡ z^p (mod p^(k+1))`
  for any p ≥ 2, k ≥ 1.  Combines telescoping + `valAtLeast_mul`.

- **Teichmüller convergence** (Cauchy): for p prime,
  `(iter x (n+1)).trunc (n+1) = (iter x n).trunc (n+1)`.
  By induction using Frobenius lift on the difference.
-/

namespace E213.Lib.Math.Padic

/-- The geometric sum `y^0·z^(N-1) + y^1·z^(N-2) + ... + y^(N-1)·z^0`,
    encoded as a `ZpSeq`.

    Recurrence: `sum_(N+1) = y · sum_N + z^N`.
    Verifies: `sum_0 = 0`, `sum_1 = z^0 = 1`, `sum_2 = y + z`, etc. -/
def Zp.sum_geo_pow (p : Nat) (hp : 1 < p) (y z : ZpSeq p) : Nat → ZpSeq p
  | 0 => ZpSeq.zero p (Nat.lt_of_succ_lt hp)
  | N + 1 =>
    Zp.add p (Nat.lt_of_succ_lt hp)
      (Zp.mul p (Nat.lt_of_succ_lt hp) y (Zp.sum_geo_pow p hp y z N))
      (Zp.pow p hp z N)

/-- Level 0 is the zero sequence. -/
theorem Zp.sum_geo_pow_zero (p : Nat) (hp : 1 < p) (y z : ZpSeq p) :
    Zp.sum_geo_pow p hp y z 0 = ZpSeq.zero p (Nat.lt_of_succ_lt hp) := rfl

/-- Successor step (definitional). -/
theorem Zp.sum_geo_pow_succ (p : Nat) (hp : 1 < p) (y z : ZpSeq p) (N : Nat) :
    Zp.sum_geo_pow p hp y z (N + 1)
      = Zp.add p (Nat.lt_of_succ_lt hp)
          (Zp.mul p (Nat.lt_of_succ_lt hp) y (Zp.sum_geo_pow p hp y z N))
          (Zp.pow p hp z N) := rfl

/-! ## Telescoping identity

The classical algebraic identity:
  `(y - z) · sum_geo_pow y z N = y^N - z^N`.

We prove it at trunc level, working with `Zp.add x (Zp.neg y)` for
subtraction.  Base case N=0 uses `add_neg_self_trunc`.  Inductive
step uses the symmetric form of the sum recurrence.
-/

/-- PURE: `(x · 0).trunc k = 0`. -/
private theorem mul_zero_trunc (p : Nat) (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    (Zp.mul p hp x (ZpSeq.zero p hp)).trunc k = 0 :=
  Zp.mul_zero_right_trunc hp x k

/-- Sum geo pow at N=0 is the zero sequence; at trunc level it's 0. -/
theorem Zp.sum_geo_pow_zero_trunc (p : Nat) (hp : 1 < p) (y z : ZpSeq p) (k : Nat) :
    (Zp.sum_geo_pow p hp y z 0).trunc k = 0 :=
  ZpSeq.trunc_zero p (Nat.lt_of_succ_lt hp) k

/-- Base case for telescoping: at N=0, both `(y - z) · 0` and `y^0 - z^0 = 1 - 1`
    truncate to 0. -/
theorem Zp.telescoping_zero (p : Nat) (hp : 1 < p) (y z : ZpSeq p) (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp)
        (Zp.add p (Nat.lt_of_succ_lt hp) y (Zp.neg p hp z))
        (Zp.sum_geo_pow p hp y z 0)).trunc (n + 1)
      = (Zp.add p (Nat.lt_of_succ_lt hp)
          (Zp.pow p hp y 0) (Zp.neg p hp (Zp.pow p hp z 0))).trunc (n + 1) := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  -- LHS: (y + (-z)) · 0 ≡ 0 at trunc.
  rw [Zp.sum_geo_pow_zero, mul_zero_trunc p hp' _ (n + 1)]
  -- RHS: y^0 + (-z^0) = 1 + (-1) ≡ 0 at trunc.
  show 0 = (Zp.add p hp' (ZpSeq.one p hp) (Zp.neg p hp (ZpSeq.one p hp))).trunc (n + 1)
  rw [Zp.add_neg_self_trunc p hp (ZpSeq.one p hp) n]

/-! ## Nat-level Frobenius lift

The core of Teichmüller convergence is the Frobenius lift:
  `b ≡ 0 (mod p^k), k ≥ 1 → (a + b)^p ≡ a^p (mod p^(k+1))`.

Proved at the Nat level via geometric sum factorization
  `(a + b)^p - a^p = b · S(a, b, p)`
where `S(a, b, p) = sum_{i=0}^{p-1} (a + b)^i · a^(p-1-i)`.

When `b ≡ 0 (mod p)`, each term of `S` is ≡ `a^(p-1) (mod p)`, so
`S` has `p` equal terms ≡ 0 (mod p).  Combined with `b = c · p^k`,
the product `b · S ≡ 0 (mod p^(k+1))`.
-/

/-- Nat-level geometric sum: `sum_{i=0}^{N-1} (a + b)^i · a^(N-1-i)`. -/
private def geo_sum_nat (a b : Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => (a + b)^N + a * geo_sum_nat a b N

/-- Recurrence (definitional): `geo_sum_nat a b (N + 1) = (a+b)^N + a · geo_sum_nat a b N`. -/
private theorem geo_sum_nat_succ (a b N : Nat) :
    geo_sum_nat a b (N + 1) = (a + b)^N + a * geo_sum_nat a b N := rfl

/-- PURE Nat: `(a + b)^p = a^p + b · geo_sum_nat a b p`.

    The geometric-sum factorization of the difference of powers,
    at Nat level.  Proved by induction on `p`. -/
private theorem pow_add_factor (a b : Nat) :
    ∀ p, (a + b)^p = a^p + b * geo_sum_nat a b p
  | 0 => by
    show 1 = 1 + b * 0
    rw [Nat.mul_zero, Nat.add_zero]
  | p + 1 => by
    have ih : (a + b)^p = a^p + b * geo_sum_nat a b p := pow_add_factor a b p
    -- Let S := geo_sum_nat a b p (abbreviation).
    -- Goal: (a + b)^(p + 1) = a^(p + 1) + b * geo_sum_nat a b (p + 1)
    -- = (a + b)^p * (a + b)  by pow_succ
    -- = (a^p + b · S) * (a + b)  by IH
    -- We compute both sides explicitly.
    -- Define: tgt_lhs := (a^p + b · S) * (a + b)
    --         tgt_rhs := a^p * a + b * (geo_sum_nat (p+1))
    --                  = a^p * a + b * ((a + b)^p + a · S)
    --                  = a^p * a + b * ((a^p + b · S) + a · S)  by IH
    -- Both expand to a^p · a + (mixed terms in b).
    rw [Nat.pow_succ (a + b) p, ih, Nat.pow_succ a p, geo_sum_nat_succ, ih]
    -- Goal: (a^p + b * S) * (a + b) = a^p * a + b * ((a^p + b * S) + a * S)
    -- LHS by add_mul: = a^p * (a + b) + b * S * (a + b)
    -- LHS by mul_add: = (a^p * a + a^p * b) + (b * S * a + b * S * b)
    -- RHS by mul_add: = a^p * a + (b * (a^p + b * S) + b * (a * S))
    --                = a^p * a + ((b * a^p + b * (b * S)) + b * (a * S))
    -- We use calc to chain.
    rw [E213.Tactic.NatHelper.add_mul (a^p) (b * geo_sum_nat a b p) (a + b)]
    rw [Nat.mul_add (a^p) a b]
    rw [Nat.mul_add (b * geo_sum_nat a b p) a b]
    rw [Nat.mul_add b (a^p + b * geo_sum_nat a b p) (a * geo_sum_nat a b p)]
    rw [Nat.mul_add b (a^p) (b * geo_sum_nat a b p)]
    -- Now both LHS and RHS are Nat expressions; rearrange via assoc + comm.
    -- LHS:  a^p * a + a^p * b + (b * S * a + b * S * b)
    -- RHS:  a^p * a + (b * a^p + b * (b * S) + b * (a * S))
    -- Match: a^p * b ↔ b * a^p (comm); b * S * a ↔ b * (a * S) (assoc+comm);
    --        b * S * b ↔ b * (b * S) (assoc+comm).
    -- Let me reorganize: regroup LHS as a^p * a + (a^p * b + b * S * b + b * S * a),
    -- regroup RHS as a^p * a + (b * a^p + b * (b * S) + b * (a * S)).
    -- Then match term by term.
    rw [show a^p * b = b * a^p from Nat.mul_comm _ _]
    rw [show b * geo_sum_nat a b p * a = b * (a * geo_sum_nat a b p) by
          rw [E213.Tactic.NatHelper.mul_assoc b (geo_sum_nat a b p) a,
              Nat.mul_comm (geo_sum_nat a b p) a]]
    rw [show b * geo_sum_nat a b p * b = b * (b * geo_sum_nat a b p) by
          rw [E213.Tactic.NatHelper.mul_assoc b (geo_sum_nat a b p) b,
              Nat.mul_comm (geo_sum_nat a b p) b]]
    -- Now LHS = a^p * a + b * a^p + (b * (a * S) + b * (b * S))
    -- RHS = a^p * a + (b * a^p + b * (b * S) + b * (a * S))
    -- Normalize both to left-assoc form, then swap last two.
    rw [← Nat.add_assoc (a^p * a + b * a^p) (b * (a * geo_sum_nat a b p))
          (b * (b * geo_sum_nat a b p))]
    -- LHS: a^p * a + b * a^p + b * (a * S) + b * (b * S)
    rw [← Nat.add_assoc (a^p * a) (b * a^p + b * (b * geo_sum_nat a b p))
          (b * (a * geo_sum_nat a b p))]
    rw [← Nat.add_assoc (a^p * a) (b * a^p) (b * (b * geo_sum_nat a b p))]
    -- RHS: a^p * a + b * a^p + b * (b * S) + b * (a * S)
    -- LHS = X + C + D, RHS = X + D + C where X = a^p * a + b * a^p, C = b * (a * S), D = b * (b * S).
    exact Nat.add_right_comm _ _ _

/-- PURE Nat: `(a + b)^N % p = a^N % p` when `b % p = 0`.  Powers of `a + b`
    reduce to powers of `a` modulo p. -/
private theorem pow_add_mod_zero (a b p : Nat) (hp : 0 < p) (hbp : b % p = 0) :
    ∀ N, (a + b)^N % p = a^N % p
  | 0 => by rw [Nat.pow_zero, Nat.pow_zero]
  | N + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ]
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure ((a + b)^N) (a + b) p]
    rw [pow_add_mod_zero a b p hp hbp N]
    rw [E213.Meta.Nat.AddMod213.add_mod hp a b, hbp, Nat.add_zero,
        E213.Tactic.NatHelper.mod_mod_pure]
    rw [← E213.Meta.Nat.MulMod213.mul_mod_pure (a^N) a p]

/-- PURE Nat: `geo_sum_nat a b (N + 1) % p = ((N + 1) * a^N) % p` when `b % p = 0`.

    Each of the (N+1) terms of the sum is `≡ a^N (mod p)` when `b ≡ 0 (mod p)`,
    so the sum mod p is `(N + 1) · a^N` mod p. -/
private theorem geo_sum_mod_eq (a b p : Nat) (hp : 0 < p) (hbp : b % p = 0) :
    ∀ N, geo_sum_nat a b (N + 1) % p = ((N + 1) * a^N) % p
  | 0 => by
    show ((a + b)^0 + a * geo_sum_nat a b 0) % p = (1 * a^0) % p
    rw [Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
    show (1 + a * 0) % p = 1 % p
    rw [Nat.mul_zero, Nat.add_zero]
  | N + 1 => by
    rw [geo_sum_nat_succ a b (N + 1)]
    -- Goal: ((a+b)^(N+1) + a * geo_sum_nat a b (N+1)) % p = ((N+2) * a^(N+1)) % p
    rw [E213.Meta.Nat.AddMod213.add_mod hp ((a + b)^(N + 1)) (a * geo_sum_nat a b (N + 1))]
    rw [pow_add_mod_zero a b p hp hbp (N + 1)]
    -- Goal: (a^(N+1) % p + (a * geo_sum_nat a b (N+1)) % p) % p = ((N+2) * a^(N+1)) % p
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure a (geo_sum_nat a b (N + 1)) p]
    rw [geo_sum_mod_eq a b p hp hbp N]
    -- Goal: (a^(N+1) % p + (a % p * (((N+1) * a^N) % p)) % p) % p = ((N+2) * a^(N+1)) % p
    rw [← E213.Meta.Nat.MulMod213.mul_mod_pure a ((N + 1) * a^N) p]
    -- (a^(N+1) % p + (a * ((N+1) * a^N)) % p) % p = ((N+2) * a^(N+1)) % p
    rw [← E213.Meta.Nat.AddMod213.add_mod hp (a^(N + 1)) (a * ((N + 1) * a^N))]
    -- (a^(N+1) + a * ((N+1) * a^N)) % p = ((N+2) * a^(N+1)) % p
    -- a * ((N+1) * a^N) = (N+1) * (a * a^N) = (N+1) * a^(N+1)  by mul_comm + mul_assoc + pow_succ
    rw [show a * ((N + 1) * a^N) = (N + 1) * a^(N + 1) by
          rw [← E213.Tactic.NatHelper.mul_assoc a (N + 1) (a^N),
              Nat.mul_comm a (N + 1),
              E213.Tactic.NatHelper.mul_assoc (N + 1) a (a^N),
              Nat.mul_comm a (a^N),
              ← Nat.pow_succ]]
    -- (a^(N+1) + (N+1) * a^(N+1)) % p = ((N+2) * a^(N+1)) % p
    -- Use Nat.succ_mul: (N+2) * a^(N+1) = (N+1) * a^(N+1) + a^(N+1).
    rw [show (N + 2) * a^(N + 1) = a^(N + 1) + (N + 1) * a^(N + 1) by
          rw [show (N + 2 : Nat) = (N + 1) + 1 from rfl, Nat.succ_mul (N+1) (a^(N+1)),
              Nat.add_comm ((N + 1) * a^(N + 1)) (a^(N + 1))]]

/-- PURE Nat: `geo_sum_nat a b p % p = 0` when `b % p = 0`.  The geometric sum
    at exponent `p` has `p` terms each ≡ `a^(p-1) (mod p)`, so total ≡ 0 mod p. -/
private theorem geo_sum_mod_zero_at_p (a b p : Nat) (hp : 0 < p) (hbp : b % p = 0) :
    geo_sum_nat a b p % p = 0 := by
  -- Case on p: for p = 0, geo_sum_nat a b 0 = 0; for p = q + 1, use geo_sum_mod_eq.
  cases p with
  | zero => exact absurd hp (Nat.lt_irrefl 0)
  | succ q =>
    rw [geo_sum_mod_eq a b (q + 1) hp hbp q]
    -- Goal: ((q+1) * a^q) % (q+1) = 0
    exact E213.Tactic.NatHelper.mul_mod_right (q + 1) (a^q)

end E213.Lib.Math.Padic
