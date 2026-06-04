import E213.Meta.Int213.Core

/-!
# PolyZ — integer-coefficient polynomials (∅-axiom)

A polynomial over `ℤ` is a coefficient list `[a₀, a₁, …]` (low-to-high), evaluated by
Horner.  This is the **entry ring** for the characteristic-polynomial determinant
`det (xI − M)` used in the integer Cayley–Hamilton theorem (`Linalg213.CayleyHamilton`,
toward the C-finite Hadamard product `cfiniteZ_mul`).

The companion `Polynomial213` is over `ℕ`; the characteristic polynomial needs **signed**
coefficients (`xI − M`), so this module rebuilds the layer over `ℤ`.

All operations come with an `eval` **soundness** lemma (each op commutes with evaluation),
making `PolyZ` a commutative-ring reflection of `Int`.  All ∅-axiom (over `Int213`).
-/

namespace E213.Lib.Math.PolyZ

/-- An integer polynomial: coefficient list, low-to-high (`[a₀, a₁, a₂] = a₀ + a₁x + a₂x²`). -/
abbrev PolyZ := List Int

/-- Horner evaluation `p(x)`. -/
def eval : PolyZ → Int → Int
  | [],     _ => 0
  | a :: p, x => a + x * eval p x

/-- The constant polynomial `c`. -/
def C (c : Int) : PolyZ := [c]

/-- The polynomial `X`. -/
def Xp : PolyZ := [0, 1]

/-- Coefficient-wise addition. -/
def addP : PolyZ → PolyZ → PolyZ
  | [],     q      => q
  | a :: p, []     => a :: p
  | a :: p, b :: q => (a + b) :: addP p q

/-- Coefficient-wise negation. -/
def negP (p : PolyZ) : PolyZ := p.map (fun a => - a)

/-- Scalar multiple. -/
def scaleP (k : Int) (p : PolyZ) : PolyZ := p.map (fun a => k * a)

/-- Multiply by `X` (shift up by one degree). -/
def shiftP (p : PolyZ) : PolyZ := 0 :: p

/-- Polynomial multiplication. -/
def mulP : PolyZ → PolyZ → PolyZ
  | [],     _ => []
  | a :: p, q => addP (scaleP a q) (shiftP (mulP p q))

/-- The `k`-th coefficient (`0` past the end). -/
def coeff : PolyZ → Nat → Int
  | [],     _     => 0
  | a :: _, 0     => a
  | _ :: p, k + 1 => coeff p k

/-! ## ℤ helpers (`Int213` lacks `add_zero` / `mul_zero` / `one_mul`) -/

/-- `a + 0 = a`. -/
theorem add_zero' (a : Int) : a + 0 = a := by
  rw [E213.Meta.Int213.add_comm, E213.Meta.Int213.zero_add]

/-- `a * 0 = 0`. -/
theorem mul_zero' (a : Int) : a * 0 = 0 := by
  rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.zero_mul]

/-- `1 * a = a`. -/
theorem one_mul' (a : Int) : 1 * a = a := by
  rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.mul_one]

/-! ## Evaluation soundness — each operation commutes with `eval` -/

/-- `eval` of a constant. -/
theorem eval_C (c : Int) (x : Int) : eval (C c) x = c := by
  show c + x * eval [] x = c
  rw [show eval [] x = 0 from rfl, mul_zero', add_zero']

/-- `eval` of `X`. -/
theorem eval_Xp (x : Int) : eval Xp x = x := by
  show (0 : Int) + x * (1 + x * eval [] x) = x
  rw [show eval [] x = 0 from rfl, mul_zero', add_zero', E213.Meta.Int213.mul_one,
      E213.Meta.Int213.zero_add]

/-- ★ `eval` is additive. -/
theorem eval_addP : ∀ (p q : PolyZ) (x : Int), eval (addP p q) x = eval p x + eval q x
  | [],     q,      x => by
    show eval q x = 0 + eval q x
    rw [E213.Meta.Int213.zero_add]
  | a :: p, [],     x => by
    show a + x * eval p x = (a + x * eval p x) + 0
    rw [add_zero']
  | a :: p, b :: q, x => by
    show (a + b) + x * eval (addP p q) x = (a + x * eval p x) + (b + x * eval q x)
    rw [eval_addP p q x, E213.Meta.Int213.mul_add]
    -- (a+b) + (x*ep + x*eq) = (a + x*ep) + (b + x*eq)
    rw [E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_assoc,
        ← E213.Meta.Int213.add_assoc b (x * eval p x), ← E213.Meta.Int213.add_assoc (x * eval p x) b,
        E213.Meta.Int213.add_comm (x * eval p x) b]

/-- ★ `eval` of a scalar multiple. -/
theorem eval_scaleP (k : Int) : ∀ (p : PolyZ) (x : Int), eval (scaleP k p) x = k * eval p x
  | [],     x => (mul_zero' k).symm
  | a :: p, x => by
    show k * a + x * eval (scaleP k p) x = k * (a + x * eval p x)
    rw [eval_scaleP k p x, E213.Meta.Int213.mul_add]
    -- k*a + x*(k*ep) = k*a + k*(x*ep)
    rw [← E213.Meta.Int213.mul_assoc x k, E213.Meta.Int213.mul_comm x k,
        E213.Meta.Int213.mul_assoc k x]

/-- `eval` of `X · p` (shift). -/
theorem eval_shiftP (p : PolyZ) (x : Int) : eval (shiftP p) x = x * eval p x := by
  show (0 : Int) + x * eval p x = x * eval p x
  rw [E213.Meta.Int213.zero_add]

/-- ★ `eval` is negation-compatible. -/
theorem eval_negP : ∀ (p : PolyZ) (x : Int), eval (negP p) x = - eval p x
  | [],     x => by
    show (0 : Int) = -0
    rw [show -(0:Int) = 0 from (E213.Meta.Int213.zero_add (-0)).symm.trans
        (E213.Meta.Int213.add_neg_cancel 0)]
  | a :: p, x => by
    show (- a) + x * eval (negP p) x = -(a + x * eval p x)
    rw [eval_negP p x, E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_add]

/-- ★★ `eval` is multiplicative. -/
theorem eval_mulP : ∀ (p q : PolyZ) (x : Int), eval (mulP p q) x = eval p x * eval q x
  | [],     q, x => by
    show (0 : Int) = 0 * eval q x
    rw [E213.Meta.Int213.zero_mul]
  | a :: p, q, x => by
    show eval (addP (scaleP a q) (shiftP (mulP p q))) x = (a + x * eval p x) * eval q x
    rw [eval_addP, eval_scaleP, eval_shiftP, eval_mulP p q x,
        E213.Meta.Int213.add_mul, E213.Meta.Int213.mul_assoc]

end E213.Lib.Math.PolyZ
