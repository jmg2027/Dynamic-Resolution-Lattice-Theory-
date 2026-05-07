import E213.Lib.Math.Functional.Norm

/-!
# Functional Analysis 213 — Linear operators (atomic, finite-grid)

213-native paradigm: a linear operator is `LinOp := (Nat → Nat) →
(Nat → Nat)`.  Identity, scalar multiplication, addition.  No
Choice-dependent extension theorems (Hahn-Banach rejected).

Atomic content:
  * `idOp`, `zeroOp` — base operators.
  * `scaleOp c` — multiply each pointwise value by `c`.
  * `addOp T U` — pointwise sum of operators.
  * `composeOp` — `T ∘ U`.
-/

namespace E213.Lib.Math.Functional.LinearOperator

open E213.Lib.Math.Functional.Norm (constFn)

/-- Type synonym for a linear operator on `Nat → Nat` grid functions. -/
abbrev LinOp := (Nat → Nat) → (Nat → Nat)

/-- Identity operator. -/
def idOp : LinOp := id

/-- Zero operator. -/
def zeroOp : LinOp := fun _ => fun _ => 0

/-- Scalar multiplication operator. -/
def scaleOp (c : Nat) : LinOp := fun f i => c * f i

/-- Sum of operators. -/
def addOp (T U : LinOp) : LinOp := fun f i => T f i + U f i

/-- Composition. -/
def composeOp (T U : LinOp) : LinOp := fun f => T (U f)

/-- ★ Identity at any function returns it (rfl). -/
theorem id_at (f : Nat → Nat) : idOp f = f := rfl

/-- ★ Zero operator returns the zero function (rfl). -/
theorem zero_at (f : Nat → Nat) (i : Nat) : zeroOp f i = 0 := rfl

/-- ★ Scale operator on a constant: `scaleOp c (constFn d) i = c * d`. -/
theorem scale_const (c d i : Nat) :
    scaleOp c (constFn d) i = c * d := rfl

/-- ★ Composition is associative on functions (rfl). -/
theorem compose_assoc_pointwise (T U V : LinOp) (f : Nat → Nat) :
    composeOp T (composeOp U V) f = composeOp (composeOp T U) V f := rfl

/-- ★ `idOp ∘ T = T` pointwise (rfl). -/
theorem compose_id_left (T : LinOp) (f : Nat → Nat) :
    composeOp idOp T f = T f := rfl

end E213.Lib.Math.Functional.LinearOperator
