import E213.Meta.Int213.Core

/-!
# `PolyInt2` — a ∅-axiom reflection prover for *bivariate* `Int` polynomial identities

Lean-core `ring`/`omega` are unavailable or `propext`-dirty, and the `quad_norm` tactic
(`Meta/Tactic/QuadNorm`) uses `simp`+`omega` (axiom-dirty); `Meta/Nat/PolyNat` is
∅-axiom but `Nat`-only and *univariate*.  Many `Int` identities — e.g. the Eisenstein
norm positive-definiteness `2·(a²−ab+b²) = a² + b² + (a−b)²` — are **bivariate over `Int`
with subtraction**, outside both.  This file fills the gap by **reflection**, two Horner
layers: a polynomial in `X` whose coefficients are polynomials in `Y` (each a `List Int`),
normalised so that two expressions with the same normal form evaluate equally — the
normal forms are closed `List (List Int)`, so equality is `rfl` (no `decide`, `propext`,
`Classical`, or `omega`).  Subtraction is handled by a `neg` constructor over `Int`
coefficients.

Usage (manual reification — mirror each side of the goal as a `PE2` over `X`, `Y`):

```lean
example (a b : Int) : 2*(a*a - a*b + b*b) = a*a + b*b + (a - b)*(a - b) :=
  poly_id2
    (.mul (.C 2) (.add (.add (.mul .X .X) (.neg (.mul .X .Y))) (.mul .Y .Y)))
    (.add (.add (.mul .X .X) (.mul .Y .Y)) (.mul (.add .X (.neg .Y)) (.add .X (.neg .Y))))
    rfl a b
```

All zero-axiom.
-/

namespace E213.Meta.Int213.PolyInt2

open E213.Meta.Int213
  (add_mul mul_add mul_assoc mul_left_comm zero_add zero_mul neg_add mul_neg
   add_comm add_assoc mul_one)

/-! ## §0 — a small additive rearrangement helper -/

private theorem add4_comm (a b c d : Int) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc a b (c + d), ← add_assoc b c d, add_comm b c, add_assoc c b d,
      ← add_assoc a c (b + d)]

/-! ## §1 — the `Y` layer: univariate `Int` polynomials (coefficient ring) -/

/-- Horner evaluation of a `Y`-polynomial (low degree first). -/
def yEval : List Int → Int → Int
  | [],      _ => 0
  | c :: cs, y => c + y * yEval cs y

def yAdd : List Int → List Int → List Int
  | [],      q       => q
  | a :: p,  []      => a :: p
  | a :: p,  b :: q  => (a + b) :: yAdd p q

def yScale : Int → List Int → List Int
  | _, []      => []
  | a, b :: q  => a * b :: yScale a q

def yMul : List Int → List Int → List Int
  | [],     _ => []
  | a :: p, q => yAdd (yScale a q) (0 :: yMul p q)

def yNeg : List Int → List Int
  | []     => []
  | a :: p => (-a) :: yNeg p

theorem yScale_eval (a : Int) : ∀ q y, yEval (yScale a q) y = a * yEval q y
  | [],     _ => by show (0 : Int) = a * 0; rw [Int.mul_zero]
  | b :: q, y => by
    show a * b + y * yEval (yScale a q) y = a * (b + y * yEval q y)
    rw [yScale_eval a q y, mul_add a b (y * yEval q y)]
    congr 1
    exact mul_left_comm y a (yEval q y)

theorem yAdd_eval : ∀ p q y, yEval (yAdd p q) y = yEval p y + yEval q y
  | [],     q,      y => by show yEval q y = 0 + yEval q y; rw [zero_add]
  | a :: p, [],     y => by show yEval (a::p) y = yEval (a::p) y + 0; rw [Int.add_zero]
  | a :: p, b :: q, y => by
    show (a + b) + y * yEval (yAdd p q) y
       = (a + y * yEval p y) + (b + y * yEval q y)
    rw [yAdd_eval p q y, mul_add y (yEval p y) (yEval q y),
        add4_comm a (y * yEval p y) b (y * yEval q y)]

theorem yMul_eval : ∀ p q y, yEval (yMul p q) y = yEval p y * yEval q y
  | [],     q, y => by show (0 : Int) = 0 * yEval q y; rw [zero_mul]
  | a :: p, q, y => by
    show yEval (yAdd (yScale a q) (0 :: yMul p q)) y = (a + y * yEval p y) * yEval q y
    rw [yAdd_eval, yScale_eval]
    show a * yEval q y + (0 + y * yEval (yMul p q) y) = (a + y * yEval p y) * yEval q y
    rw [zero_add, yMul_eval p q y, add_mul a (y * yEval p y) (yEval q y),
        mul_assoc y (yEval p y) (yEval q y)]

theorem yNeg_eval : ∀ q y, yEval (yNeg q) y = -(yEval q y)
  | [],     y => by show (0 : Int) = -(0 : Int); rw [Int.neg_zero]
  | a :: q, y => by
    show -a + y * yEval (yNeg q) y = -(a + y * yEval q y)
    rw [yNeg_eval q y, neg_add a (y * yEval q y), mul_neg y (yEval q y)]

/-! ## §2 — the `X` layer: polynomials in `X` with `Y`-polynomial coefficients -/

def eval2 : List (List Int) → Int → Int → Int
  | [],      _, _ => 0
  | c :: cs, x, y => yEval c y + x * eval2 cs x y

def add2 : List (List Int) → List (List Int) → List (List Int)
  | [],      q       => q
  | a :: p,  []      => a :: p
  | a :: p,  b :: q  => yAdd a b :: add2 p q

def scale2 : List Int → List (List Int) → List (List Int)
  | _, []       => []
  | a, c :: cs  => yMul a c :: scale2 a cs

def mul2 : List (List Int) → List (List Int) → List (List Int)
  | [],     _ => []
  | a :: p, q => add2 (scale2 a q) ([] :: mul2 p q)

def neg2 : List (List Int) → List (List Int)
  | []      => []
  | c :: cs => yNeg c :: neg2 cs

theorem scale2_eval (a : List Int) : ∀ q x y,
    eval2 (scale2 a q) x y = yEval a y * eval2 q x y
  | [],      x, y => by show (0 : Int) = yEval a y * 0; rw [Int.mul_zero]
  | c :: cs, x, y => by
    show yEval (yMul a c) y + x * eval2 (scale2 a cs) x y
       = yEval a y * (yEval c y + x * eval2 cs x y)
    rw [yMul_eval a c y, scale2_eval a cs x y, mul_add (yEval a y) (yEval c y) (x * eval2 cs x y)]
    congr 1
    exact mul_left_comm x (yEval a y) (eval2 cs x y)

theorem add2_eval : ∀ p q x y, eval2 (add2 p q) x y = eval2 p x y + eval2 q x y
  | [],      q,      x, y => by show eval2 q x y = 0 + eval2 q x y; rw [zero_add]
  | a :: p,  [],     x, y => by
    show eval2 (a::p) x y = eval2 (a::p) x y + 0; rw [Int.add_zero]
  | a :: p,  b :: q, x, y => by
    show yEval (yAdd a b) y + x * eval2 (add2 p q) x y
       = (yEval a y + x * eval2 p x y) + (yEval b y + x * eval2 q x y)
    rw [yAdd_eval a b y, add2_eval p q x y, mul_add x (eval2 p x y) (eval2 q x y),
        add4_comm (yEval a y) (x * eval2 p x y) (yEval b y) (x * eval2 q x y)]

theorem mul2_eval : ∀ p q x y, eval2 (mul2 p q) x y = eval2 p x y * eval2 q x y
  | [],     q, x, y => by show (0 : Int) = 0 * eval2 q x y; rw [zero_mul]
  | a :: p, q, x, y => by
    show eval2 (add2 (scale2 a q) ([] :: mul2 p q)) x y
       = (yEval a y + x * eval2 p x y) * eval2 q x y
    rw [add2_eval, scale2_eval]
    show yEval a y * eval2 q x y + (0 + x * eval2 (mul2 p q) x y)
       = (yEval a y + x * eval2 p x y) * eval2 q x y
    rw [zero_add, mul2_eval p q x y, add_mul (yEval a y) (x * eval2 p x y) (eval2 q x y),
        mul_assoc x (eval2 p x y) (eval2 q x y)]

theorem neg2_eval : ∀ p x y, eval2 (neg2 p) x y = -(eval2 p x y)
  | [],      x, y => by show (0 : Int) = -(0 : Int); rw [Int.neg_zero]
  | c :: cs, x, y => by
    show yEval (yNeg c) y + x * eval2 (neg2 cs) x y = -(yEval c y + x * eval2 cs x y)
    rw [yNeg_eval c y, neg2_eval cs x y, neg_add (yEval c y) (x * eval2 cs x y),
        mul_neg x (eval2 cs x y)]

/-! ## §3 — the expression type, normal form, and the driver -/

/-- A bivariate `Int` polynomial expression: variables `X`, `Y`, constants, sums,
    products, and negation (so subtraction `a - b = a + (-b)`). -/
inductive PE2 where
  | X   : PE2
  | Y   : PE2
  | C   : Int → PE2
  | add : PE2 → PE2 → PE2
  | mul : PE2 → PE2 → PE2
  | neg : PE2 → PE2

def PE2.eval : PE2 → Int → Int → Int
  | .X,       x, _ => x
  | .Y,       _, y => y
  | .C c,     _, _ => c
  | .add a b, x, y => a.eval x y + b.eval x y
  | .mul a b, x, y => a.eval x y * b.eval x y
  | .neg a,   x, y => -(a.eval x y)

def PE2.norm : PE2 → List (List Int)
  | .X       => [[0], [1]]
  | .Y       => [[0, 1]]
  | .C c     => [[c]]
  | .add a b => add2 a.norm b.norm
  | .mul a b => mul2 a.norm b.norm
  | .neg a   => neg2 a.norm

theorem norm_eval2 : ∀ (e : PE2) x y, eval2 e.norm x y = e.eval x y
  | .X,       x, y => by
    show (0 + y * 0) + x * ((1 + y * 0) + x * 0) = x
    rw [Int.mul_zero, Int.mul_zero, Int.add_zero, Int.add_zero,
        Int.add_zero, mul_one, zero_add]
  | .Y,       x, y => by
    show (0 + y * (1 + y * 0)) + x * 0 = y
    rw [Int.mul_zero, Int.mul_zero, Int.add_zero, Int.add_zero, mul_one, zero_add]
  | .C c,     x, y => by
    show (c + y * 0) + x * 0 = c
    rw [Int.mul_zero, Int.mul_zero, Int.add_zero, Int.add_zero]
  | .add a b, x, y => by
    show eval2 (add2 a.norm b.norm) x y = a.eval x y + b.eval x y
    rw [add2_eval, norm_eval2 a x y, norm_eval2 b x y]
  | .mul a b, x, y => by
    show eval2 (mul2 a.norm b.norm) x y = a.eval x y * b.eval x y
    rw [mul2_eval, norm_eval2 a x y, norm_eval2 b x y]
  | .neg a,   x, y => by
    show eval2 (neg2 a.norm) x y = -(a.eval x y)
    rw [neg2_eval, norm_eval2 a x y]

/-- ★★★ **The reflection driver.**  Two bivariate `Int` polynomial expressions with
    equal normal forms evaluate equally everywhere.  Apply with `h := rfl` (the normal
    forms are closed `List (List Int)`): `poly_id2 eL eR rfl x y : eL.eval x y =
    eR.eval x y`, where each `PE2.eval` reduces by `rfl` to the mirrored `Int`
    expression. -/
theorem poly_id2 (eL eR : PE2) (h : eL.norm = eR.norm) (x y : Int) :
    eL.eval x y = eR.eval x y := by
  rw [← norm_eval2 eL x y, ← norm_eval2 eR x y, h]

end E213.Meta.Int213.PolyInt2
