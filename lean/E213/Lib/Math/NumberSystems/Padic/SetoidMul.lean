import E213.Lib.Math.NumberSystems.Padic.SetoidAssoc
/-!
# Zp.mul identities at the Setoid level (ZpSeqEquiv)

The multiplicative twin of `SetoidAssoc.lean`.  `SetoidAssoc` closed the
**additive abelian group** on `ZpSeq` modulo `ZpSeqEquiv` (assoc, comm,
zero, inverse); this file closes the **multiplicative monoid + the
distributive laws**, completing the **commutative ring** structure.

Every identity lifts a truncation-level fact (`Arith.lean`'s ring-quotient
theorems `Zp.mul_trunc_comm` / `Zp.mul_trunc_assoc` / `Zp.mul_add_trunc` /
`Zp.add_mul_trunc`, all of which descend `Zp.mul` to `ℤ/p^n` via
`Zp.mul_trunc`) through `ZpSeqEquiv.of_trunc_all`: agreement at every
truncation IS the digit-pointwise equivalence (`SetoidFramework`), funext-
and propext-free.

The multiplicative unit `Zp.mul one x ≈ x` uses `Zp.mul_trunc_one_left`
(at `n+1`, `one.trunc (n+1) = 1`, so the product truncates back to `x`).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.SetoidMul

open E213.Lib.Math.NumberSystems.Padic.SetoidFramework (ZpSeqEquiv)

/-! ## §1 — multiplicative commutativity / associativity at the Setoid level -/

/-- ★★★★ **Zp.mul commutativity at the Setoid level**: `x · y ≈ y · x`. -/
theorem zp_mul_comm_equiv (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp x y) (Zp.mul p hp y x) :=
  ZpSeqEquiv.of_trunc_all hp (fun n => Zp.mul_trunc_comm p hp x y n)

/-- ★★★★ **Zp.mul associativity at the Setoid level**: `(x · y) · z ≈ x · (y · z)`. -/
theorem zp_mul_assoc_equiv (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp (Zp.mul p hp x y) z)
                (Zp.mul p hp x (Zp.mul p hp y z)) :=
  ZpSeqEquiv.symm (ZpSeqEquiv.of_trunc_all hp (fun n => Zp.mul_trunc_assoc p hp x y z n))

/-! ## §2 — the distributive laws at the Setoid level -/

/-- ★★★★ **Left distributivity at the Setoid level**: `x · (y + z) ≈ x · y + x · z`. -/
theorem zp_mul_add_distrib_equiv (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp x (Zp.add p hp y z))
                (Zp.add p hp (Zp.mul p hp x y) (Zp.mul p hp x z)) :=
  ZpSeqEquiv.of_trunc_all hp (fun n => Zp.mul_add_trunc p hp x y z n)

/-- ★★★★ **Right distributivity at the Setoid level**: `(x + y) · z ≈ x · z + y · z`. -/
theorem zp_add_mul_distrib_equiv (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp (Zp.add p hp x y) z)
                (Zp.add p hp (Zp.mul p hp x z) (Zp.mul p hp y z)) :=
  ZpSeqEquiv.of_trunc_all hp (fun n => Zp.add_mul_trunc p hp x y z n)

/-! ## §3 — the multiplicative unit at the Setoid level -/

/-- `(one · x).trunc n = x.trunc n` at every level: at `n+1` the unit truncates to `1`
    (`trunc_one_succ`) and the product mod `p^(n+1)` is `x.trunc (n+1)` itself
    (`trunc_lt_p_pow`); at `n = 0` both truncations are `0`. -/
theorem mul_one_left_trunc_eq (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ∀ n, (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x).trunc n = x.trunc n
  | 0 => rfl
  | n + 1 => by
    rw [Zp.mul_trunc_one_left hp x (n + 1), ZpSeq.trunc_one_succ p hp n, Nat.one_mul]
    exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow (Nat.lt_of_succ_lt hp) x (n + 1))

/-- ★★★★ **Multiplicative left identity at the Setoid level**: `one · x ≈ x`. -/
theorem zp_mul_one_left_equiv (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x) x :=
  ZpSeqEquiv.of_trunc_all (Nat.lt_of_succ_lt hp) (mul_one_left_trunc_eq p hp x)

/-! ## §4 — Capstone: ZpSeq / ZpSeqEquiv is a commutative ring -/

/-- ★★★★★ **Setoid-level commutative-ring capstone for `ZpSeq`**.

    Bundles the additive abelian group (from `SetoidAssoc.zp_add_setoid_group_capstone`:
    add assoc / comm / zero / negation) with the **multiplicative monoid** (comm / assoc /
    one) and the two **distributive laws** — the full statement that
    `(ZpSeq p, ZpSeqEquiv)` is a commutative ring, realized digit-pointwise without
    funext / propext / Quot.sound.

    Together with `SetoidAlgebra.setoid_algebra_capstone` (every operation *respects*
    `ZpSeqEquiv`), this is the complete ring structure descending to the quotient. -/
theorem zp_setoid_commRing_capstone
    (p : Nat) (hp : 1 < p) (x y z : ZpSeq p) :
    -- additive abelian group (assoc, comm, zero, inverse)
    ( ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) (Zp.add p (Nat.lt_of_succ_lt hp) x y) z)
                  (Zp.add p (Nat.lt_of_succ_lt hp) x (Zp.add p (Nat.lt_of_succ_lt hp) y z))
      ∧ ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) x y)
                    (Zp.add p (Nat.lt_of_succ_lt hp) y x)
      ∧ ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) (ZpSeq.zero p (Nat.lt_of_succ_lt hp)) x) x
      ∧ ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) x (Zp.neg p hp x))
                    (ZpSeq.zero p (Nat.lt_of_succ_lt hp)) )
    -- multiplicative commutative monoid (comm, assoc, one)
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x y) (Zp.mul p (Nat.lt_of_succ_lt hp) y x)
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.mul p (Nat.lt_of_succ_lt hp) x y) z)
                  (Zp.mul p (Nat.lt_of_succ_lt hp) x (Zp.mul p (Nat.lt_of_succ_lt hp) y z))
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x) x
    -- distributivity (left + right)
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x (Zp.add p (Nat.lt_of_succ_lt hp) y z))
                  (Zp.add p (Nat.lt_of_succ_lt hp)
                    (Zp.mul p (Nat.lt_of_succ_lt hp) x y)
                    (Zp.mul p (Nat.lt_of_succ_lt hp) x z))
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.add p (Nat.lt_of_succ_lt hp) x y) z)
                  (Zp.add p (Nat.lt_of_succ_lt hp)
                    (Zp.mul p (Nat.lt_of_succ_lt hp) x z)
                    (Zp.mul p (Nat.lt_of_succ_lt hp) y z)) := by
  refine ⟨SetoidAssoc.zp_add_setoid_group_capstone p hp x y z, ?_, ?_, ?_, ?_, ?_⟩
  · exact zp_mul_comm_equiv p (Nat.lt_of_succ_lt hp) x y
  · exact zp_mul_assoc_equiv p (Nat.lt_of_succ_lt hp) x y z
  · exact zp_mul_one_left_equiv p hp x
  · exact zp_mul_add_distrib_equiv p (Nat.lt_of_succ_lt hp) x y z
  · exact zp_add_mul_distrib_equiv p (Nat.lt_of_succ_lt hp) x y z

end E213.Lib.Math.NumberSystems.Padic.SetoidMul
