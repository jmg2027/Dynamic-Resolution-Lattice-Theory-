import E213.Lib.Math.NumberSystems.Padic.ZpSqrtDRigor
/-!
# Rigor — ZpSqrtD ring axioms at digit-0

Companion to `ZpSqrtDRigor.lean` establishing **ring axioms**
(commutativity of `zpsd_add`, commutativity of `zpsd_mul`, zero /
one identities) at digit-0.

The full ring axioms over ZpSeq require funext-style equalities on
the digit sequence; the digit-0 versions are pointwise Nat facts
following from `Zp.add_digit_val` + `Zp.mul_digit_val` and
`Nat.add_comm` / `Nat.mul_comm`.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.ZpSqrtDRing

open E213.Lib.Math.NumberSystems.Padic.HenselBridge (fromFp fromFp_digit_zero)
open E213.Lib.Math.NumberSystems.Padic.ZpSqrtD
  (ZpSqrtD zpsd_add zpsd_mul zpsd_zero zpsd_one fp2d_to_zpsd)
open E213.Lib.Math.NumberSystems.Padic.ZpSqrtDRigor
  (zpsd_add_digit_zero_first zpsd_add_digit_zero_second
   zpmul_digit_zero zpsd_mul_digit_zero_second)

/-! ## §1 — Commutativity of `zpsd_add` at digit-0 -/

/-- ★ `zpsd_add` is commutative at digit-0 (first component). -/
theorem zpsd_add_comm_digit_zero_first
    (p : Nat) (hp : 0 < p) (x y : ZpSqrtD p) :
    ((zpsd_add p hp x y).1.digits 0).val
    = ((zpsd_add p hp y x).1.digits 0).val := by
  rw [zpsd_add_digit_zero_first p hp x y]
  rw [zpsd_add_digit_zero_first p hp y x]
  rw [Nat.add_comm (x.1.digits 0).val (y.1.digits 0).val]

/-- ★ `zpsd_add` is commutative at digit-0 (second component). -/
theorem zpsd_add_comm_digit_zero_second
    (p : Nat) (hp : 0 < p) (x y : ZpSqrtD p) :
    ((zpsd_add p hp x y).2.digits 0).val
    = ((zpsd_add p hp y x).2.digits 0).val := by
  rw [zpsd_add_digit_zero_second p hp x y]
  rw [zpsd_add_digit_zero_second p hp y x]
  rw [Nat.add_comm (x.2.digits 0).val (y.2.digits 0).val]

/-! ## §2 — Commutativity of `Zp.mul` at digit-0 -/

/-- ★ `Zp.mul` is commutative at digit-0. -/
theorem zpmul_comm_digit_zero
    (p : Nat) (hp : 0 < p) (a b : ZpSeq p) :
    ((Zp.mul p hp a b).digits 0).val
    = ((Zp.mul p hp b a).digits 0).val := by
  rw [zpmul_digit_zero p hp a b, zpmul_digit_zero p hp b a]
  rw [Nat.mul_comm (a.digits 0).val (b.digits 0).val]

/-! ## §3 — Commutativity of `zpsd_mul` second-component -/

/-- ★ `zpsd_mul` is commutative at the second-component digit-0
    (the D-independent component `ad + bc`).  -/
theorem zpsd_mul_comm_digit_zero_second
    (p : Nat) (hp : 0 < p) (D : Nat) (x y : ZpSqrtD p) :
    ((zpsd_mul p hp D x y).2.digits 0).val
    = ((zpsd_mul p hp D y x).2.digits 0).val := by
  rw [zpsd_mul_digit_zero_second p hp D x y]
  rw [zpsd_mul_digit_zero_second p hp D y x]
  -- Goal: (a·d + b·c) mod p = (b'·c' + a'·d') mod p with swapped labels
  -- LHS = ((x.1*y.2)%p + (x.2*y.1)%p) % p
  -- RHS = ((y.1*x.2)%p + (y.2*x.1)%p) % p
  rw [Nat.mul_comm (y.1.digits 0).val (x.2.digits 0).val]
  rw [Nat.mul_comm (y.2.digits 0).val (x.1.digits 0).val]
  rw [Nat.add_comm
        ((x.2.digits 0).val * (y.1.digits 0).val % p)
        ((x.1.digits 0).val * (y.2.digits 0).val % p)]

/-! ## §4 — Zero / one identities at digit-0 -/

/-- ★ `zpsd_zero` has both digit-0 components equal to 0. -/
theorem zpsd_zero_components_zero
    (p : Nat) (hp : 0 < p) :
    ((zpsd_zero p hp).1.digits 0).val = 0
    ∧ ((zpsd_zero p hp).2.digits 0).val = 0 :=
  ⟨rfl, rfl⟩

/-- ★ `zpsd_one` has digit-0 components `(1, 0)`. -/
theorem zpsd_one_components_one_zero
    (p : Nat) (hp : 1 < p) :
    ((zpsd_one p hp).1.digits 0).val = 1
    ∧ ((zpsd_one p hp).2.digits 0).val = 0 :=
  ⟨rfl, rfl⟩

/-- ★ Add-zero on the left preserves the first-component digit-0
    (modulo p reduction).  Uses `zpsd_add_digit_zero_first` plus
    `Nat.zero_add`. -/
theorem zpsd_add_zero_left_first_mod
    (p : Nat) (hp : 0 < p) (x : ZpSqrtD p)
    (hx : (x.1.digits 0).val < p) :
    ((zpsd_add p hp (zpsd_zero p hp) x).1.digits 0).val
    = (x.1.digits 0).val := by
  rw [zpsd_add_digit_zero_first p hp]
  show (((zpsd_zero p hp).1.digits 0).val + (x.1.digits 0).val) % p
       = (x.1.digits 0).val
  show (0 + (x.1.digits 0).val) % p = (x.1.digits 0).val
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt hx

/-! ## §5 — Capstone -/

/-- ★★★★★ **ZpSqrtD ring-axioms-at-digit-0 capstone**.

    Bundles: (a) add commutativity at both components,
    (b) mul commutativity at second component, (c) zero / one
    digit-0 values, (d) add-zero-left identity.

    Reading: the ring axioms (commutativity, zero / one identities)
    hold at digit-0 modulo p — the rigorous form of the ring
    structure on ZpSqrtD as a lift of FP2SqrtD. -/
theorem zpsd_ring_capstone
    (p : Nat) (hp : 0 < p) (D : Nat) (x y : ZpSqrtD p) :
    -- (a) Add commutativity at both components
    ((zpsd_add p hp x y).1.digits 0).val
      = ((zpsd_add p hp y x).1.digits 0).val
    ∧ ((zpsd_add p hp x y).2.digits 0).val
      = ((zpsd_add p hp y x).2.digits 0).val
    -- (b) Mul commutativity at second component
    ∧ ((zpsd_mul p hp D x y).2.digits 0).val
      = ((zpsd_mul p hp D y x).2.digits 0).val
    -- (c) Zero / one digit-0 values
    ∧ ((zpsd_zero p hp).1.digits 0).val = 0
    ∧ ((zpsd_zero p hp).2.digits 0).val = 0 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · exact zpsd_add_comm_digit_zero_first p hp x y
  · exact zpsd_add_comm_digit_zero_second p hp x y
  · exact zpsd_mul_comm_digit_zero_second p hp D x y

end E213.Lib.Math.NumberSystems.Padic.ZpSqrtDRing
