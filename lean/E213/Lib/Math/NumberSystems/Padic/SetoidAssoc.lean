import E213.Lib.Math.NumberSystems.Padic.SetoidAlgebra
import E213.Meta.Nat.AddMod213
/-!
# Zp.add associativity via Setoid + trunc arithmetic

Closes `Zp.add` associativity at the Setoid level (ZpSeqEquiv)
using `Zp.add_trunc` to bypass carry-chain blow-up.

  `Zp.add_trunc`: `(Zp.add x y).trunc n = (x.trunc n + y.trunc n) % p^n`

This descends addition to `ℤ/p^n`, where associativity is just
`Nat.add_assoc` + mod-stable arithmetic.  From there, equal
truncations at every n imply equal digits (since
`digits k = (trunc (k+1) - trunc k) / p^k`), which gives
`ZpSeqEquiv` directly.

The Setoid Framework + truncation arithmetic is the
**LensMap composition** form of `Zp.add` associativity: the
algebraic identity is realised at the equivalence level via the
truncation projection.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.SetoidAssoc

open E213.Lib.Math.NumberSystems.Padic.SetoidFramework (ZpSeqEquiv)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)

/-! ## §1 — Truncation-level associativity -/

/-- ★★★ `Zp.add` associativity at the truncation level (every n):

  `(Zp.add (Zp.add x y) z).trunc n = (Zp.add x (Zp.add y z)).trunc n`

Both sides reduce to `(x.trunc n + y.trunc n + z.trunc n) % p^n`
via `Zp.add_trunc` + Nat add_mod chain. -/
theorem add_assoc_trunc (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) (n : Nat) :
    (Zp.add p hp (Zp.add p hp x y) z).trunc n
    = (Zp.add p hp x (Zp.add p hp y z)).trunc n := by
  -- LHS: ((x.trunc n + y.trunc n) % p^n + z.trunc n) % p^n
  rw [Zp.add_trunc p hp (Zp.add p hp x y) z n]
  rw [Zp.add_trunc p hp x y n]
  -- = (x.trunc n + y.trunc n + z.trunc n) % p^n
  --   via add_mod_gen: ((a + b) % m + c) % m = (a + b + c) % m
  have lhs_eq : ((x.trunc n + y.trunc n) % p^n + z.trunc n) % p^n
              = (x.trunc n + y.trunc n + z.trunc n) % p^n := by
    rw [add_mod_gen ((x.trunc n + y.trunc n) % p^n) (z.trunc n) (p^n)]
    rw [mod_mod (x.trunc n + y.trunc n) (p^n)]
    rw [← add_mod_gen (x.trunc n + y.trunc n) (z.trunc n) (p^n)]
  rw [lhs_eq]
  -- RHS: (x.trunc n + (y.trunc n + z.trunc n) % p^n) % p^n
  rw [Zp.add_trunc p hp x (Zp.add p hp y z) n]
  rw [Zp.add_trunc p hp y z n]
  -- = (x.trunc n + y.trunc n + z.trunc n) % p^n
  have rhs_eq : (x.trunc n + (y.trunc n + z.trunc n) % p^n) % p^n
              = (x.trunc n + y.trunc n + z.trunc n) % p^n := by
    rw [add_mod_gen (x.trunc n) ((y.trunc n + z.trunc n) % p^n) (p^n)]
    rw [mod_mod (y.trunc n + z.trunc n) (p^n)]
    rw [← add_mod_gen (x.trunc n) (y.trunc n + z.trunc n) (p^n)]
    -- (x + (y + z)) = (x + y + z) by Nat.add_assoc
    rw [← Nat.add_assoc]
  rw [rhs_eq]

/-- Re-export `add_left_cancel_pure` from the Meta layer. -/
private theorem add_left_cancel_pure {a b c : Nat}
    (h : a + b = a + c) : b = c :=
  E213.Tactic.NatHelper.add_left_cancel_pure h

/-! ## §2 — Trunc-equality at consecutive levels implies digit-equality -/

/-- Helper: if two sequences have equal trunc at both `k` and `k+1`,
    then their digit at `k` matches.

    Derivation: `trunc (k+1) = trunc k + digit_k * p^k`.  So
    `digit_k * p^k = trunc (k+1) - trunc k`, and dividing by `p^k`
    extracts `digit_k`. -/
theorem digits_eq_of_trunc_eq (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (k : Nat)
    (h_k : x.trunc k = y.trunc k)
    (h_k1 : x.trunc (k + 1) = y.trunc (k + 1)) :
    x.digits k = y.digits k := by
  -- trunc (k+1) = trunc k + digits k · p^k
  apply Fin.ext
  -- Derive (x.digits k).val * p^k = (y.digits k).val * p^k
  have hx : x.trunc (k + 1) = x.trunc k + (x.digits k).val * p^k := rfl
  have hy : y.trunc (k + 1) = y.trunc k + (y.digits k).val * p^k := rfl
  -- From h_k1: x.trunc k + a*p^k = y.trunc k + b*p^k
  -- + h_k: x.trunc k = y.trunc k
  -- so a*p^k = b*p^k
  have h_sum : x.trunc k + (x.digits k).val * p^k
             = y.trunc k + (y.digits k).val * p^k := by
    rw [← hx, ← hy, h_k1]
  rw [h_k] at h_sum
  -- Now: y.trunc k + a*p^k = y.trunc k + b*p^k → a*p^k = b*p^k
  have h_eq_mul : (x.digits k).val * p^k = (y.digits k).val * p^k :=
    add_left_cancel_pure h_sum
  -- Cancel p^k (which is nonzero since p > 0)
  have h_pos : 0 < p^k := Nat.pos_pow_of_pos k hp
  exact Nat.eq_of_mul_eq_mul_right h_pos h_eq_mul

/-! ## §3 — Zp.add associativity at ZpSeqEquiv -/

/-- ★★★★★ **Zp.add associativity at the Setoid level**:
    `Zp.add (Zp.add x y) z ≈ Zp.add x (Zp.add y z)`.

    Proof: trunc-level associativity (Pattern: Residual Induction,
    truncation arithmetic bypasses carry blow-up) + the standard
    "equal trunc at every n implies equal digits at every k"
    extraction. -/
theorem zp_add_assoc_equiv (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.add p hp (Zp.add p hp x y) z)
                (Zp.add p hp x (Zp.add p hp y z)) := by
  intro k
  -- Use digits_eq_of_trunc_eq with n = k and n = k+1
  exact digits_eq_of_trunc_eq p hp _ _ k
    (add_assoc_trunc p hp x y z k)
    (add_assoc_trunc p hp x y z (k + 1))

/-! ## §4 — Bonus: Zp.add commutativity at the Setoid level -/

/-- Zp.add commutativity at the truncation level via Nat.add_comm. -/
theorem add_comm_trunc (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (n : Nat) :
    (Zp.add p hp x y).trunc n = (Zp.add p hp y x).trunc n := by
  rw [Zp.add_trunc, Zp.add_trunc]
  rw [Nat.add_comm (x.trunc n) (y.trunc n)]

/-- ★★★★ **Zp.add commutativity at the Setoid level**:
    `Zp.add x y ≈ Zp.add y x`. -/
theorem zp_add_comm_equiv (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    ZpSeqEquiv (Zp.add p hp x y) (Zp.add p hp y x) := by
  intro k
  exact digits_eq_of_trunc_eq p hp _ _ k
    (add_comm_trunc p hp x y k)
    (add_comm_trunc p hp x y (k + 1))

/-! ## §5 — Zp.add identity (zero) at the Setoid level -/

/-- Zero left identity at the truncation level. -/
theorem add_zero_left_trunc (p : Nat) (hp : 0 < p) (x : ZpSeq p) (n : Nat) :
    (Zp.add p hp (ZpSeq.zero p hp) x).trunc n = x.trunc n % p^n := by
  rw [Zp.add_trunc]
  rw [ZpSeq.trunc_zero p hp n]
  rw [Nat.zero_add]

/-- ★★★★ **Zp.add zero left identity** at the Setoid level
    (when `x.trunc n < p^n` for all n, which holds for all ZpSeq). -/
theorem zp_add_zero_left_equiv (p : Nat) (hp : 0 < p) (x : ZpSeq p) :
    ZpSeqEquiv (Zp.add p hp (ZpSeq.zero p hp) x) x := by
  intro k
  apply digits_eq_of_trunc_eq p hp _ _ k
  · rw [add_zero_left_trunc p hp x k]
    exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow hp x k)
  · rw [add_zero_left_trunc p hp x (k + 1)]
    exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow hp x (k + 1))

/-! ## §6 — Capstone -/

/-- ★★★★★ **Setoid-level ring laws for Zp.add capstone**.

    Closes the open follow-up "the chain abstracting Zp.add's
    associativity law into a LensMap composition law".  All three ring laws (assoc, comm, zero)
    realized at the Setoid level via:

      (a) Truncation arithmetic (Pattern: Residual Induction)
      (b) Trunc-equality at consecutive levels implies digit equality
      (c) ZpSeqEquiv lift

    Bundles: add_assoc, add_comm, add_zero — full additive
    monoid structure on ZpSeq modulo ZpSeqEquiv. -/
theorem zp_add_setoid_monoid_capstone
    (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    -- (a) Associativity
    ZpSeqEquiv (Zp.add p hp (Zp.add p hp x y) z)
                (Zp.add p hp x (Zp.add p hp y z))
    -- (b) Commutativity
    ∧ ZpSeqEquiv (Zp.add p hp x y) (Zp.add p hp y x)
    -- (c) Zero left identity
    ∧ ZpSeqEquiv (Zp.add p hp (ZpSeq.zero p hp) x) x := by
  refine ⟨?_, ?_, ?_⟩
  · exact zp_add_assoc_equiv p hp x y z
  · exact zp_add_comm_equiv p hp x y
  · exact zp_add_zero_left_equiv p hp x

/-! ## §7 — Zp.add additive inverse at the Setoid level -/

/-- ★★★★ **Additive inverse** at the Setoid level: `x + (−x) ≈ 0`.  Completes the
    additive abelian group on `ZpSeq` modulo `ZpSeqEquiv` (monoid + inverse), lifting the
    per-truncation cancellation `Zp.add_neg_self_trunc` via `of_trunc_all` (funext-free). -/
theorem zp_add_neg_self_equiv (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) x (Zp.neg p hp x))
                (ZpSeq.zero p (Nat.lt_of_succ_lt hp)) :=
  SetoidFramework.ZpSeqEquiv.of_trunc_all (Nat.lt_of_succ_lt hp) (fun n => by
    cases n with
    | zero => rfl
    | succ m =>
        rw [Zp.add_neg_self_trunc p hp x m,
            ZpSeq.trunc_zero p (Nat.lt_of_succ_lt hp) (m + 1)])

/-- ★★★★★ **Setoid-level additive abelian group capstone for `Zp.add`**: extends the
    monoid capstone with the additive inverse — assoc, comm, zero, and `x + (−x) ≈ 0`. -/
theorem zp_add_setoid_group_capstone
    (p : Nat) (hp : 1 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) (Zp.add p (Nat.lt_of_succ_lt hp) x y) z)
                (Zp.add p (Nat.lt_of_succ_lt hp) x (Zp.add p (Nat.lt_of_succ_lt hp) y z))
    ∧ ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) x y)
                  (Zp.add p (Nat.lt_of_succ_lt hp) y x)
    ∧ ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) (ZpSeq.zero p (Nat.lt_of_succ_lt hp)) x) x
    ∧ ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) x (Zp.neg p hp x))
                  (ZpSeq.zero p (Nat.lt_of_succ_lt hp)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zp_add_assoc_equiv p (Nat.lt_of_succ_lt hp) x y z
  · exact zp_add_comm_equiv p (Nat.lt_of_succ_lt hp) x y
  · exact zp_add_zero_left_equiv p (Nat.lt_of_succ_lt hp) x
  · exact zp_add_neg_self_equiv p hp x

end E213.Lib.Math.NumberSystems.Padic.SetoidAssoc
