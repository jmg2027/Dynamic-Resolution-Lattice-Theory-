import E213.Lib.Math.Linalg213.DetN
import E213.Lib.Math.PolyZ

/-!
# Linalg213 — the polynomial determinant `pdet` and its evaluation soundness

`pdet n A` is the determinant of a matrix `A` whose entries are integer polynomials
(`PolyZ`), defined by the same row-0 cofactor recursion as `DetN.det`.  Its single defining
property is **evaluation soundness**:

  `eval (pdet n A) x = det n (fun i j => eval (A i j) x)`

i.e. evaluating the polynomial determinant at `x` is the integer determinant of the
entry-wise evaluated matrix.  This lets the integer Cayley–Hamilton argument get the
characteristic polynomial `χ = pdet (xI − M)` **as actual integer coefficients**, while
proving identities about it by evaluation (reusing the `Int` determinant theory) rather than
re-deriving cofactor/adjugate theory over `PolyZ`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.PolyDet

open E213.Lib.Math.Linalg213.DetN (det cofSum minor colShift altSign det_congr)
open E213.Lib.Math.PolyZ (PolyZ eval C addP scaleP mulP eval_C eval_addP eval_scaleP eval_mulP)

/-- The `(0,j)`-minor of a polynomial matrix (drop row 0, column `j`). -/
def pminor (A : Nat → Nat → PolyZ) (j : Nat) : Nat → Nat → PolyZ :=
  fun i l => A (i + 1) (colShift j l)

/-- Cofactor sum for the polynomial determinant (row-0 Laplace, mirrors `DetN.cofSum`). -/
def pcofSum (pdetN : (Nat → Nat → PolyZ) → PolyZ) (A : Nat → Nat → PolyZ) : Nat → PolyZ
  | 0     => []
  | c + 1 => addP (pcofSum pdetN A c) (scaleP (altSign c) (mulP (A 0 c) (pdetN (pminor A c))))

/-- The **polynomial determinant** (row-0 cofactor recursion over `PolyZ`). -/
def pdet : Nat → (Nat → Nat → PolyZ) → PolyZ
  | 0,     _ => C 1
  | n + 1, A => pcofSum (pdet n) A (n + 1)

/-- Entry-wise evaluation of a polynomial matrix at `x`. -/
def evalMat (A : Nat → Nat → PolyZ) (x : Int) : Nat → Nat → Int := fun i j => eval (A i j) x

/-- `evalMat` commutes with taking a minor (pointwise). -/
theorem evalMat_pminor (A : Nat → Nat → PolyZ) (j : Nat) (x : Int) (i l : Nat) :
    evalMat (pminor A j) x i l = minor (evalMat A x) j i l := rfl

/-- `eval` of the cofactor sum is the integer cofactor sum of the evaluated matrix. -/
theorem eval_pcofSum (n : Nat) (A : Nat → Nat → PolyZ) (x : Int)
    (ih : ∀ (B : Nat → Nat → PolyZ), eval (pdet n B) x = det n (evalMat B x)) :
    ∀ (c : Nat), eval (pcofSum (pdet n) A c) x = cofSum (det n) (evalMat A x) c
  | 0     => rfl
  | c + 1 => by
    show eval (addP (pcofSum (pdet n) A c) (scaleP (altSign c) (mulP (A 0 c) (pdet n (pminor A c))))) x
       = cofSum (det n) (evalMat A x) c + altSign c * eval (A 0 c) x * det n (minor (evalMat A x) c)
    rw [eval_addP, eval_pcofSum n A x ih c, eval_scaleP, eval_mulP, ih (pminor A c),
        det_congr n (evalMat_pminor A c x),
        ← E213.Meta.Int213.mul_assoc (altSign c) (eval (A 0 c) x)
          (det n (minor (evalMat A x) c))]

/-- ★★ **Evaluation soundness**: `eval (pdet n A) x = det n (evalMat A x)`.  Evaluating the
    polynomial determinant equals the integer determinant of the evaluated matrix. -/
theorem eval_pdet : ∀ (n : Nat) (A : Nat → Nat → PolyZ) (x : Int),
    eval (pdet n A) x = det n (evalMat A x)
  | 0,     A, x => eval_C 1 x
  | n + 1, A, x => eval_pcofSum n A x (fun B => eval_pdet n B x) (n + 1)

end E213.Lib.Math.Linalg213.PolyDet
