import E213.Lib.Math.NumberSystems.Padic.Foundation
import E213.Lib.Math.NumberSystems.Padic.Arith
import E213.Lib.Math.NumberSystems.Padic.Pow
import E213.Lib.Math.NumberSystems.Padic.Norm
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

namespace E213.Lib.Math.NumberSystems.Padic

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
  cases p with
  | zero => exact absurd hp (Nat.lt_irrefl 0)
  | succ q =>
    rw [geo_sum_mod_eq a b (q + 1) hp hbp q]
    exact E213.Tactic.NatHelper.mul_mod_right (q + 1) (a^q)

/-- PURE Nat: `p^k % p = 0` for `k ≥ 1`. -/
private theorem pow_mod_zero (p k : Nat) (hk : 1 ≤ k) : p^k % p = 0 := by
  cases k with
  | zero => exact absurd hk (Nat.not_succ_le_zero 0)
  | succ q =>
    rw [Nat.pow_succ, Nat.mul_comm (p^q) p]
    exact E213.Tactic.NatHelper.mul_mod_right p (p^q)

/-- **Nat-level Frobenius lift**: `b % p^k = 0, k ≥ 1 →
    (a + b)^p % p^(k+1) = a^p % p^(k+1)` for any `p ≥ 1`.

    Combines `pow_add_factor` (factorization) and `geo_sum_mod_zero_at_p`
    (sum divisibility), giving `(a + b)^p - a^p = b · S` divisible by
    `p^(k+1)`. -/
private theorem frobenius_lift_nat (a b p k : Nat) (hp : 0 < p) (hk : 1 ≤ k)
    (hbk : b % p^k = 0) :
    (a + b)^p % p^(k + 1) = a^p % p^(k + 1) := by
  -- b = p^k * c where c = b / p^k.
  have hb_eq : b = p^k * (b / p^k) := by
    have := E213.Meta.Nat.AddMod213.div_add_mod b (p^k)
    rw [hbk, Nat.add_zero] at this
    exact this.symm
  -- b % p = 0 (since p | p^k | b).
  have hb_p : b % p = 0 := by
    rw [hb_eq]
    -- (p^k * c) % p = ((p^k % p) * c) % p = (0 * c) % p = 0
    rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure (p^k) (b / p^k) p,
        pow_mod_zero p k hk, Nat.zero_mul, E213.Tactic.NatHelper.zero_mod]
  -- S := geo_sum_nat a b p satisfies S % p = 0.
  have hS_mod_p : geo_sum_nat a b p % p = 0 := geo_sum_mod_zero_at_p a b p hp hb_p
  -- (a + b)^p = a^p + b * S.
  rw [pow_add_factor a b p]
  -- Want: (a^p + b * S) % p^(k+1) = a^p % p^(k+1).
  -- b * S = (p^k * c) * S = p^k * (c * S).
  -- (c * S) % p = 0 (since S % p = 0).
  -- So c * S = p * m for some m, hence b * S = p^k * p * m = p^(k+1) * m.
  have hcS_mod : ((b / p^k) * geo_sum_nat a b p) % p = 0 := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure (b / p^k) (geo_sum_nat a b p) p,
        hS_mod_p, Nat.mul_zero, E213.Tactic.NatHelper.zero_mod]
  -- b * S = p^k * ((b / p^k) * S).  Use congrArg to avoid mass-substituting b.
  have hbS_eq : b * geo_sum_nat a b p
              = p^k * ((b / p^k) * geo_sum_nat a b p) := by
    have h1 : b * geo_sum_nat a b p
            = (p^k * (b / p^k)) * geo_sum_nat a b p :=
      congrArg (· * geo_sum_nat a b p) hb_eq
    rw [h1, E213.Tactic.NatHelper.mul_assoc (p^k) (b / p^k) (geo_sum_nat a b p)]
  -- Rewrite b * S in goal.
  rw [hbS_eq]
  -- Goal: (a^p + p^k * ((b/p^k) * S)) % p^(k+1) = a^p % p^(k+1)
  -- Strategy: (p^k * X) % p^(k+1) = ((X % p) * p^k) by mul_pow_succ_mod style,
  --           but we have X = (b/p^k) * S with X % p = 0, so this gives 0.
  -- Compute (p^k * X) % p^(k+1):
  -- (p^k * X) = p^k * (p * (X / p) + X % p) = p^k * p * (X / p) + p^k * (X % p)
  --           = p^(k+1) * (X / p) + p^k * (X % p) = p^(k+1) * (X / p) (since X % p = 0).
  -- So (p^k * X) % p^(k+1) = 0.
  have hX_div : (b / p^k) * geo_sum_nat a b p
              = p * ((b / p^k) * geo_sum_nat a b p / p) := by
    have := E213.Meta.Nat.AddMod213.div_add_mod
              ((b / p^k) * geo_sum_nat a b p) p
    rw [hcS_mod, Nat.add_zero] at this
    exact this.symm
  rw [hX_div]
  -- Goal: (a^p + p^k * (p * ((b/p^k) * S / p))) % p^(k+1) = a^p % p^(k+1)
  -- p^k * (p * Y) = p^(k+1) * Y.
  rw [← E213.Tactic.NatHelper.mul_assoc (p^k) p _]
  rw [show p^k * p = p^(k + 1) from (Nat.pow_succ p k).symm]
  -- Goal: (a^p + p^(k+1) * Y) % p^(k+1) = a^p % p^(k+1)
  rw [Nat.mul_comm (p^(k+1)) _]
  exact E213.Tactic.NatHelper.add_mul_mod_self_pure (a^p)
    (p^(k+1)) (b / p^k * geo_sum_nat a b p / p)

/-! ## Lift to ZpSeq + Teichmüller convergence -/

/-- **ZpSeq-level Frobenius lift**: if `y.trunc k = z.trunc k` (i.e.,
    `y ≡ z (mod p^k)`) and `k ≥ 1`, then `(y^p).trunc (k+1) = (z^p).trunc (k+1)`
    (i.e., `y^p ≡ z^p (mod p^(k+1))`). -/
theorem Zp.frobenius_lift (p : Nat) (hp : 1 < p) (y z : ZpSeq p) (k : Nat)
    (hk : 1 ≤ k)
    (h_yz : y.trunc k = z.trunc k) :
    (Zp.pow p hp y p).trunc (k + 1) = (Zp.pow p hp z p).trunc (k + 1) := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  -- (y^p).trunc (k+1) = (y.trunc (k+1))^p % p^(k+1) by pow_trunc.
  rw [Zp.pow_trunc p hp y (k + 1) p, Zp.pow_trunc p hp z (k + 1) p]
  -- Want: (y.trunc(k+1))^p % p^(k+1) = (z.trunc(k+1))^p % p^(k+1).
  -- y.trunc(k+1) = y.trunc k + (y.digits k).val · p^k = a + dy · p^k where a := y.trunc k.
  -- z.trunc(k+1) = z.trunc k + (z.digits k).val · p^k = a + dz · p^k (using h_yz).
  -- Apply frobenius_lift_nat with `a` common, `b_y = dy · p^k`, `b_z = dz · p^k`.
  -- Both b_y and b_z are divisible by p^k.
  -- Let a := y.trunc k.  Then z.trunc k = a by h_yz.
  -- y.trunc (k + 1) = a + (y.digits k).val * p^k.
  have hy_form : y.trunc (k + 1) = y.trunc k + (y.digits k).val * p^k := rfl
  have hz_form : z.trunc (k + 1) = y.trunc k + (z.digits k).val * p^k := by
    show z.trunc k + (z.digits k).val * p^k = y.trunc k + (z.digits k).val * p^k
    rw [h_yz]
  rw [hy_form, hz_form]
  -- Both LHS and RHS now have form `(a + d · p^k)^p % p^(k+1)`.
  -- Apply frobenius_lift_nat to each: equals `a^p % p^(k+1)`.
  have h_y : ((y.digits k).val * p^k) % p^k = 0 := by
    rw [Nat.mul_comm (y.digits k).val (p^k)]
    exact E213.Tactic.NatHelper.mul_mod_right (p^k) (y.digits k).val
  have h_z : ((z.digits k).val * p^k) % p^k = 0 := by
    rw [Nat.mul_comm (z.digits k).val (p^k)]
    exact E213.Tactic.NatHelper.mul_mod_right (p^k) (z.digits k).val
  rw [frobenius_lift_nat (y.trunc k) ((y.digits k).val * p^k) p k hp' hk h_y]
  rw [frobenius_lift_nat (y.trunc k) ((z.digits k).val * p^k) p k hp' hk h_z]

/-- **Teichmüller iteration is Cauchy**: for `p ≥ 1`,
    `(teichmuller_iter x (n + 1)).trunc (n + 1) = (teichmuller_iter x n).trunc (n + 1)`.

    Equivalent: `iter x (n + 1) ≡ iter x n (mod p^(n+1))`.

    Proof by induction on n:
    - Base n = 0: `(iter x 1).trunc 1 = (iter x 0).trunc 1` by Fermat at digit 0
      (`pow_p_trunc_one`).
    - Step n → n+1: by IH `iter x (n + 1) ≡ iter x n (mod p^(n+1))`.
      Apply Frobenius lift (with k = n + 1 ≥ 1) to get
      `(iter x (n + 1))^p ≡ (iter x n)^p (mod p^(n + 2))`, which is
      `iter x (n + 2) ≡ iter x (n + 1) (mod p^(n + 2))`. -/
theorem Zp.teichmuller_iter_cauchy (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m → m < p
                  → (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout m p).1 = 1) :
    ∀ n, (Zp.teichmuller_iter p hp x (n + 1)).trunc (n + 1)
       = (Zp.teichmuller_iter p hp x n).trunc (n + 1)
  | 0 => by
    -- iter x 1 = x^p, iter x 0 = x.  Goal: (x^p).trunc 1 = x.trunc 1.
    show (Zp.pow p hp x p).trunc 1 = x.trunc 1
    exact Zp.pow_p_trunc_one p hp x h_prime_gcd
  | n + 1 => by
    have hp' : 0 < p := Nat.lt_of_succ_lt hp
    have ih := Zp.teichmuller_iter_cauchy p hp x h_prime_gcd n
    -- ih : (iter x (n+1)).trunc (n+1) = (iter x n).trunc (n+1).
    -- Goal: (iter x (n+2)).trunc (n+2) = (iter x (n+1)).trunc (n+2).
    -- iter x (n+2) = (iter x (n+1))^p, iter x (n+1) = (iter x n)^p.
    show (Zp.pow p hp (Zp.teichmuller_iter p hp x (n + 1)) p).trunc (n + 2)
       = (Zp.pow p hp (Zp.teichmuller_iter p hp x n) p).trunc (n + 2)
    exact Zp.frobenius_lift p hp
      (Zp.teichmuller_iter p hp x (n + 1)) (Zp.teichmuller_iter p hp x n)
      (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) ih

/-! ## The explicit Teichmüller representative `ω(x)`

The iteration `iter x n = x^(p^n)` is Cauchy (`teichmuller_iter_cauchy`):
each step fixes one more digit.  Classical theory introduces the
limit `ω(x) = lim_n x^(p^n)` via the projective limit.  Here the
limit object is the **diagonal** of the iteration —
`ω(x).digits k := (iter x k).digits k` — exactly the construction
that produced `invFull` / `sqrtFull` from their approximation
sequences (`Hensel.lean`).

Unlike `invFull`, no separate digit-stability lemma is needed: the
Cauchy identity `(iter x (n+1)).trunc (n+1) = (iter x n).trunc (n+1)`
IS the trunc recursion for the diagonal.

`ω(x)` is the unique Frobenius-fixed lift of `x.digits 0`:
- `ω(x).digits 0 = x.digits 0` (digit-0 invariant),
- `(ω(x)^p).trunc n = ω(x).trunc n` for all `n` (the defining
  idempotent `ω^p = ω`, i.e. `ω` is a `(p−1)`-th root of unity for
  units).
-/

/-- The explicit Teichmüller representative `ω(x) : ZpSeq p`, the
    diagonal of the iteration `iter x n = x^(p^n)`.  Each digit `k` is
    read off the `k`-th iterate, which has settled by level `k`
    (`teichmuller_iter_cauchy`). -/
def Zp.teichmuller (p : Nat) (hp : 1 < p) (x : ZpSeq p) : ZpSeq p where
  digits := fun k => (Zp.teichmuller_iter p hp x k).digits k

/-- **Diagonal trunc identity**: `ω(x).trunc (n+1) = (iter x n).trunc (n+1)`.
    The diagonal agrees with the level-`n` iterate up to level `n+1`,
    because each lower digit settled at its own level (Cauchy). -/
theorem Zp.teichmuller_trunc_succ (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m → m < p
                  → (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout m p).1 = 1) :
    ∀ n, (Zp.teichmuller p hp x).trunc (n + 1)
       = (Zp.teichmuller_iter p hp x n).trunc (n + 1)
  | 0 => rfl
  | n + 1 => by
    have ih := Zp.teichmuller_trunc_succ p hp x h_prime_gcd n
    -- The diagonal digit at position n+1 is, by definition, the (n+1)-th iterate's.
    have hdig : (Zp.teichmuller p hp x).digits (n + 1)
              = (Zp.teichmuller_iter p hp x (n + 1)).digits (n + 1) := rfl
    show (Zp.teichmuller p hp x).trunc (n + 1)
          + ((Zp.teichmuller p hp x).digits (n + 1)).val * p^(n + 1)
        = (Zp.teichmuller_iter p hp x (n + 1)).trunc (n + 1)
          + ((Zp.teichmuller_iter p hp x (n + 1)).digits (n + 1)).val * p^(n + 1)
    -- ih fixes the trunc; Cauchy converts (iter x (n+1)).trunc(n+1) → (iter x n).trunc(n+1).
    rw [ih, hdig, Zp.teichmuller_iter_cauchy p hp x h_prime_gcd n]

/-- **Digit-0 invariant**: `ω(x).digits 0 = x.digits 0`.  The
    representative lifts the residue `x mod p`. -/
theorem Zp.teichmuller_digit_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    (Zp.teichmuller p hp x).digits 0 = x.digits 0 := rfl

/-- `ω(x).trunc 1 = x.trunc 1` — agreement mod `p`. -/
theorem Zp.teichmuller_trunc_one (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    (Zp.teichmuller p hp x).trunc 1 = x.trunc 1 := rfl

/-- **Frobenius-fixed (idempotent `ω^p = ω`)**: for `p` prime,
    `(ω(x)^p).trunc n = ω(x).trunc n` at every level `n`.

    This is the defining property of the Teichmüller representative:
    `ω` is the unique fixed point of the Frobenius `y ↦ y^p` lifting
    `x.digits 0`.  Chain at level `n+1`:
    `(ω^p).trunc(n+1) = (ω.trunc(n+1))^p % p^(n+1)`  [pow_trunc]
    `= ((iter x n).trunc(n+1))^p % p^(n+1)`           [trunc_succ]
    `= ((iter x n)^p).trunc(n+1) = (iter x (n+1)).trunc(n+1)`  [pow_trunc, iter_succ]
    `= (iter x n).trunc(n+1) = ω.trunc(n+1)`.         [Cauchy, trunc_succ] -/
theorem Zp.teichmuller_pow_p_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m → m < p
                  → (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout m p).1 = 1) :
    ∀ n, (Zp.pow p hp (Zp.teichmuller p hp x) p).trunc n
       = (Zp.teichmuller p hp x).trunc n
  | 0 => rfl
  | n + 1 => by
    rw [Zp.pow_trunc p hp (Zp.teichmuller p hp x) (n + 1) p]
    rw [Zp.teichmuller_trunc_succ p hp x h_prime_gcd n]
    rw [← Zp.pow_trunc p hp (Zp.teichmuller_iter p hp x n) (n + 1) p]
    rw [← Zp.teichmuller_iter_succ p hp x n]
    -- `teichmuller_trunc_succ` already rewrote the RHS `ω.trunc(n+1)` to
    -- `(iter x n).trunc(n+1)`; Cauchy closes the residual goal.
    rw [Zp.teichmuller_iter_cauchy p hp x h_prime_gcd n]

/-- Smoke: the 5-adic Teichmüller representative of digit-0 = 2 has
    digit 0 equal to 2 (the lift of `2 ∈ F_5`). -/
theorem Zp.smoke_teichmuller_5_digit_two :
    ((Zp.teichmuller 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩).digits 0).val
      = 2 := rfl

/-! ## Uniqueness of the Frobenius-fixed lift

The Frobenius fix `ω^p ≡ ω` does not merely *hold* for `teichmuller`; it
**determines** the lift.  Two Frobenius-fixed sequences agreeing mod `p`
agree at every truncation — the 213-native "sequence-level" equality
(`ZpSeqEquiv`).  The engine is the Frobenius lift itself: if
`w₁ ≡ w₂ (mod p^k)` then `w₁ ≡ w₁^p ≡ w₂^p ≡ w₂ (mod p^(k+1))`, the two
outer steps by the fix and the middle by `frobenius_lift`.  No Hensel
derivative bookkeeping is needed — the fix and the lift do it. -/

/-- **Teichmüller uniqueness**: two Frobenius-fixed sequences with the
    same residue mod `p` agree at every truncation.  (`hfix` =
    `w^p ≡ w` at every level — what `teichmuller_pow_p_trunc` provides,
    and what any `(p−1)`-th root of unity satisfies.) -/
theorem Zp.teichmuller_unique (p : Nat) (hp : 1 < p) (w₁ w₂ : ZpSeq p)
    (hfix₁ : ∀ m, (Zp.pow p hp w₁ p).trunc m = w₁.trunc m)
    (hfix₂ : ∀ m, (Zp.pow p hp w₂ p).trunc m = w₂.trunc m)
    (h_res : w₁.trunc 1 = w₂.trunc 1) :
    ∀ n, w₁.trunc (n + 1) = w₂.trunc (n + 1)
  | 0 => h_res
  | m + 1 => by
    have ih := Zp.teichmuller_unique p hp w₁ w₂ hfix₁ hfix₂ h_res m
    have hf := Zp.frobenius_lift p hp w₁ w₂ (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) ih
    rw [hfix₁ (m + 2), hfix₂ (m + 2)] at hf
    exact hf

/-- **`teichmuller x` is THE Frobenius-fixed lift**: any Frobenius-fixed
    `w` with `w ≡ x (mod p)` agrees with `ω(x)` at every truncation. -/
theorem Zp.teichmuller_eq_of_fixed (p : Nat) (hp : 1 < p) (x w : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m → m < p
                  → (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout m p).1 = 1)
    (hfix : ∀ m, (Zp.pow p hp w p).trunc m = w.trunc m)
    (h_res : w.trunc 1 = x.trunc 1) (n : Nat) :
    w.trunc (n + 1) = (Zp.teichmuller p hp x).trunc (n + 1) :=
  Zp.teichmuller_unique p hp w (Zp.teichmuller p hp x) hfix
    (Zp.teichmuller_pow_p_trunc p hp x h_prime_gcd)
    (h_res.trans (Zp.teichmuller_trunc_one p hp x).symm) n

end E213.Lib.Math.NumberSystems.Padic
