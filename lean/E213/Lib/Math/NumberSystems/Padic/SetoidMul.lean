import E213.Lib.Math.NumberSystems.Padic.SetoidAssoc
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Zp.mul commutativity / associativity / identity / distributivity at the Setoid level

The multiplicative twin of `SetoidAssoc`.  The open seed flagged the sequence-level (`ZpSeqEquiv`)
multiplicative ring laws as "high difficulty — propext, or digit-wise convolution reindexing".
But `Zp.mul_trunc` descends the product to `ℤ/pⁿ`:

  `Zp.mul_trunc`: `(Zp.mul x y).trunc n = (x.trunc n · y.trunc n) % pⁿ`

so each law is just the corresponding `Nat` identity plus mod-stability (`mul_mod_left_pure`,
`mul_mod_right_pure`, `add_mod_gen`), exactly as `SetoidAssoc` did for `Zp.add`.  Trunc-equality
at every `n` then lifts to `ZpSeqEquiv` via `digits_eq_of_trunc_eq` — funext-free, ∅-axiom.

  * `mul_comm_trunc` / `zp_mul_comm_equiv`     — `x·y ≈ y·x`
  * `mul_assoc_trunc` / `zp_mul_assoc_equiv`   — `(x·y)·z ≈ x·(y·z)`
  * `mul_one_trunc` / `zp_mul_one_equiv`        — `x·1 ≈ x`  (and `one_mul`)
  * `mul_add_trunc` / `zp_mul_add_equiv`        — `x·(y+z) ≈ x·y + x·z`
  * ★★★★★ `zp_mul_setoid_comm_monoid_capstone` / `zp_setoid_comm_ring_capstone`

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.SetoidMul

open E213.Lib.Math.NumberSystems.Padic.SetoidFramework (ZpSeqEquiv)
open E213.Lib.Math.NumberSystems.Padic.SetoidAssoc (digits_eq_of_trunc_eq)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (add_mod_gen)

/-! ## §1 — commutativity -/

/-- `Zp.mul` commutativity at the truncation level, via `Nat.mul_comm`. -/
theorem mul_comm_trunc (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (n : Nat) :
    (Zp.mul p hp x y).trunc n = (Zp.mul p hp y x).trunc n := by
  rw [Zp.mul_trunc p hp x y n, Zp.mul_trunc p hp y x n, Nat.mul_comm (x.trunc n) (y.trunc n)]

/-- ★★★★ **`Zp.mul` commutativity at the Setoid level**: `x·y ≈ y·x`. -/
theorem zp_mul_comm_equiv (p : Nat) (hp : 0 < p) (x y : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp x y) (Zp.mul p hp y x) :=
  fun k => digits_eq_of_trunc_eq p hp _ _ k (mul_comm_trunc p hp x y k) (mul_comm_trunc p hp x y (k + 1))

/-! ## §2 — associativity -/

/-- `Zp.mul` associativity at the truncation level: both sides reduce to
    `(x.trunc n · y.trunc n · z.trunc n) % pⁿ`. -/
theorem mul_assoc_trunc (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) (n : Nat) :
    (Zp.mul p hp (Zp.mul p hp x y) z).trunc n = (Zp.mul p hp x (Zp.mul p hp y z)).trunc n := by
  rw [Zp.mul_trunc p hp (Zp.mul p hp x y) z n, Zp.mul_trunc p hp x y n,
      Zp.mul_trunc p hp x (Zp.mul p hp y z) n, Zp.mul_trunc p hp y z n,
      ← mul_mod_left_pure (x.trunc n * y.trunc n) (z.trunc n) (p ^ n),
      ← mul_mod_right_pure (x.trunc n) (y.trunc n * z.trunc n) (p ^ n),
      show x.trunc n * y.trunc n * z.trunc n = x.trunc n * (y.trunc n * z.trunc n) from by ring_nat]

/-- ★★★★ **`Zp.mul` associativity at the Setoid level**: `(x·y)·z ≈ x·(y·z)`. -/
theorem zp_mul_assoc_equiv (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp (Zp.mul p hp x y) z) (Zp.mul p hp x (Zp.mul p hp y z)) :=
  fun k => digits_eq_of_trunc_eq p hp _ _ k
    (mul_assoc_trunc p hp x y z k) (mul_assoc_trunc p hp x y z (k + 1))

/-! ## §3 — the multiplicative identity -/

/-- `Zp.mul x one` at the truncation level is `x` (no wraparound: `x.trunc n < pⁿ`). -/
theorem mul_one_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (n : Nat) :
    (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)).trunc n = x.trunc n := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Zp.mul_trunc p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp) (m + 1),
        ZpSeq.trunc_one_succ p hp m, Nat.mul_one]
    exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow (Nat.lt_of_succ_lt hp) x (m + 1))

/-- ★★★★ **`Zp.mul` right identity at the Setoid level**: `x·1 ≈ x`. -/
theorem zp_mul_one_equiv (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)) x :=
  fun k => digits_eq_of_trunc_eq p (Nat.lt_of_succ_lt hp) _ _ k
    (mul_one_trunc p hp x k) (mul_one_trunc p hp x (k + 1))

/-- ★★★★ **`Zp.mul` left identity at the Setoid level**: `1·x ≈ x` (via `mul_comm` + `mul_one`). -/
theorem zp_one_mul_equiv (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x) x :=
  fun k => digits_eq_of_trunc_eq p (Nat.lt_of_succ_lt hp) _ _ k
    ((mul_comm_trunc p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x k).trans (mul_one_trunc p hp x k))
    ((mul_comm_trunc p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x (k + 1)).trans
      (mul_one_trunc p hp x (k + 1)))

/-! ## §4 — left distributivity over `Zp.add` -/

/-- Left distributivity at the truncation level: both sides reduce to
    `(x.trunc n · y.trunc n + x.trunc n · z.trunc n) % pⁿ`. -/
theorem mul_add_trunc (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) (n : Nat) :
    (Zp.mul p hp x (Zp.add p hp y z)).trunc n
      = (Zp.add p hp (Zp.mul p hp x y) (Zp.mul p hp x z)).trunc n := by
  rw [Zp.mul_trunc p hp x (Zp.add p hp y z) n, Zp.add_trunc p hp y z n,
      ← mul_mod_right_pure (x.trunc n) (y.trunc n + z.trunc n) (p ^ n),
      Nat.mul_add (x.trunc n) (y.trunc n) (z.trunc n),
      Zp.add_trunc p hp (Zp.mul p hp x y) (Zp.mul p hp x z) n,
      Zp.mul_trunc p hp x y n, Zp.mul_trunc p hp x z n,
      ← add_mod_gen (x.trunc n * y.trunc n) (x.trunc n * z.trunc n) (p ^ n)]

/-- ★★★★ **Left distributivity at the Setoid level**: `x·(y+z) ≈ x·y + x·z`. -/
theorem zp_mul_add_equiv (p : Nat) (hp : 0 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p hp x (Zp.add p hp y z))
                (Zp.add p hp (Zp.mul p hp x y) (Zp.mul p hp x z)) :=
  fun k => digits_eq_of_trunc_eq p hp _ _ k
    (mul_add_trunc p hp x y z k) (mul_add_trunc p hp x y z (k + 1))

/-! ## §5 — capstones -/

/-- ★★★★★ **Setoid-level commutative monoid laws for `Zp.mul`**: assoc, comm, right identity. -/
theorem zp_mul_setoid_comm_monoid_capstone (p : Nat) (hp : 1 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.mul p (Nat.lt_of_succ_lt hp) x y) z)
                (Zp.mul p (Nat.lt_of_succ_lt hp) x (Zp.mul p (Nat.lt_of_succ_lt hp) y z))
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x y) (Zp.mul p (Nat.lt_of_succ_lt hp) y x)
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)) x :=
  ⟨zp_mul_assoc_equiv p (Nat.lt_of_succ_lt hp) x y z,
   zp_mul_comm_equiv p (Nat.lt_of_succ_lt hp) x y,
   zp_mul_one_equiv p hp x⟩

/-- ★★★★★ **Setoid-level commutative ring laws for `ZpSeq` capstone**: the additive abelian
    group (`SetoidAssoc.zp_add_setoid_group_capstone`) together with the multiplicative
    commutative monoid (assoc/comm/one) and left distributivity — `ZpSeq` modulo `ZpSeqEquiv`
    is a commutative ring.  Completes the multiplicative half the additive group left open. -/
theorem zp_setoid_comm_ring_capstone (p : Nat) (hp : 1 < p) (x y z : ZpSeq p) :
    ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.mul p (Nat.lt_of_succ_lt hp) x y) z)
                (Zp.mul p (Nat.lt_of_succ_lt hp) x (Zp.mul p (Nat.lt_of_succ_lt hp) y z))
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x y) (Zp.mul p (Nat.lt_of_succ_lt hp) y x)
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x (ZpSeq.one p hp)) x
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x (Zp.add p (Nat.lt_of_succ_lt hp) y z))
                  (Zp.add p (Nat.lt_of_succ_lt hp)
                    (Zp.mul p (Nat.lt_of_succ_lt hp) x y) (Zp.mul p (Nat.lt_of_succ_lt hp) x z)) :=
  ⟨zp_mul_assoc_equiv p (Nat.lt_of_succ_lt hp) x y z,
   zp_mul_comm_equiv p (Nat.lt_of_succ_lt hp) x y,
   zp_mul_one_equiv p hp x,
   zp_mul_add_equiv p (Nat.lt_of_succ_lt hp) x y z⟩

end E213.Lib.Math.NumberSystems.Padic.SetoidMul
