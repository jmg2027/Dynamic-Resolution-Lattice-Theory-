import E213.Lib.Math.Linalg213.Laplace
import E213.Lib.Math.Linalg213.PolyDet

/-!
# Linalg213 — the polynomial adjugate identity `(X·I − M)·adj = χ_M·I` over `ℤ[X]`

The seed of integer Cayley–Hamilton.  With the `Int` adjugate identity `M·adj M = det M·I`
(`Laplace`, holds for every integer matrix) and the polynomial-uniqueness gate (`PolyZ.coeff_unique`,
two polynomials agreeing at every integer are coefficient-equal), this lifts the adjugate identity
to the polynomial ring: the entries of `(X·I − M)·adj(X·I − M)` and of `χ_M·I` agree as integer
polynomials.

Method: matrix products / adjugates over `PolyZ` come with **evaluation soundness** (eval = the
`Int` operation on the evaluated matrix), so the lifted identity is proven by evaluating at every
`x` (the `Int` adjugate identity) and applying `coeff_unique` — no cofactor/adjugate theory is
re-derived over `PolyZ`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.CharPolyAdj

open E213.Lib.Math.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Linalg213.PermClosure (map_eq_of_mem map_map')
open E213.Lib.Math.Linalg213.DetN (det altSign colShift det_congr)
open E213.Lib.Math.Linalg213.Laplace (matMul adj minorAt matMul_adj_diag matMul_adj_offdiag)
open E213.Lib.Math.Linalg213.PolyDet
  (pdet evalMat eval_pdet charMat charPoly eval_charPoly evalMat_charMat)
open E213.Lib.Math.PolyZ
  (PolyZ eval addP mulP scaleP coeff eval_addP eval_mulP eval_scaleP coeff_unique)

/-! ## §1 — `PolyZ` matrix product and its evaluation soundness -/

/-- Sum of a list of polynomials. -/
def psumZ : List PolyZ → PolyZ
  | []      => []
  | p :: ps => addP p (psumZ ps)

/-- `eval` distributes over `psumZ`. -/
theorem eval_psumZ (x : Int) : ∀ (L : List PolyZ),
    eval (psumZ L) x = sumZ (L.map (fun p => eval p x))
  | []      => rfl
  | p :: ps => by
    show eval (addP p (psumZ ps)) x = eval p x + sumZ (ps.map (fun p => eval p x))
    rw [eval_addP, eval_psumZ x ps]

/-- Matrix product over `PolyZ`. -/
def pmatMul (n : Nat) (A B : Nat → Nat → PolyZ) : Nat → Nat → PolyZ :=
  fun i k => psumZ ((iota n).map (fun j => mulP (A i j) (B j k)))

/-- ★ **`pmatMul` evaluation soundness**: evaluating the polynomial matrix product is the integer
    matrix product of the evaluated matrices. -/
theorem eval_pmatMul (n : Nat) (A B : Nat → Nat → PolyZ) (i k : Nat) (x : Int) :
    eval (pmatMul n A B i k) x = matMul n (evalMat A x) (evalMat B x) i k := by
  show eval (psumZ ((iota n).map (fun j => mulP (A i j) (B j k)))) x
     = sumZ ((iota n).map (fun j => eval (A i j) x * eval (B j k) x))
  rw [eval_psumZ, map_map' (fun j => mulP (A i j) (B j k)) (fun p => eval p x)]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro j _
  exact eval_mulP (A i j) (B j k) x

/-! ## §2 — `PolyZ` adjugate and its evaluation soundness -/

/-- The `(i,j)`-minor of a polynomial matrix (drop row `i`, column `j`). -/
def pminorAt (i j : Nat) (A : Nat → Nat → PolyZ) : Nat → Nat → PolyZ :=
  fun i' l => A (if i' < i then i' else i' + 1) (colShift j l)

/-- The adjugate of a polynomial matrix (mirrors `Laplace.adj` over `PolyZ`). -/
def padj (n : Nat) (A : Nat → Nat → PolyZ) : Nat → Nat → PolyZ :=
  fun a b => scaleP (altSign (b + a)) (pdet n (pminorAt b a A))

/-- ★ **`padj` evaluation soundness**: `eval (padj n A a b) x = adj n (evalMat A x) a b`. -/
theorem eval_padj (n : Nat) (A : Nat → Nat → PolyZ) (a b : Nat) (x : Int) :
    eval (padj n A a b) x = adj n (evalMat A x) a b := by
  show eval (scaleP (altSign (b + a)) (pdet n (pminorAt b a A))) x
     = altSign (b + a) * det n (minorAt b a (evalMat A x))
  rw [eval_scaleP, eval_pdet]
  apply congrArg (fun z => altSign (b + a) * z)
  exact det_congr n (fun i' l => rfl)

/-! ## §3 — the polynomial adjugate identity (Cayley–Hamilton seed) -/

/-- Matrix product respects pointwise equality of its two factors (over the summation range). -/
theorem matMul_congr (n : Nat) (A A' B B' : Nat → Nat → Int) (i k : Nat)
    (hA : ∀ j, A i j = A' i j) (hB : ∀ j, B j k = B' j k) :
    matMul n A B i k = matMul n A' B' i k := by
  show sumZ ((iota n).map (fun j => A i j * B j k)) = sumZ ((iota n).map (fun j => A' i j * B' j k))
  apply congrArg sumZ
  apply map_eq_of_mem
  intro j _
  rw [hA j, hB j]

/-- The scalar matrix `χ_M · I` over `PolyZ`. -/
def charScalarId (M : Nat → Nat → Int) (N : Nat) : Nat → Nat → PolyZ :=
  fun i k => if i = k then charPoly M N else []

/-- Evaluating `(X·I − M)·adj(X·I − M)` at `x`, entry `(i,k)`, gives the `Int` adjugate value. -/
theorem padj_identity_eval (M : Nat → Nat → Int) (n i k : Nat) (hi : i < n + 1) (hk : k < n + 1)
    (x : Int) :
    eval (pmatMul (n + 1) (charMat M) (padj n (charMat M)) i k) x
      = eval (charScalarId M (n + 1) i k) x := by
  rw [eval_pmatMul,
      matMul_congr (n + 1) (evalMat (charMat M) x) (evalMat (charMat M) x)
        (evalMat (padj n (charMat M)) x) (adj n (evalMat (charMat M) x)) i k
        (fun _ => rfl) (fun j => eval_padj n (charMat M) j k x)]
  by_cases h : i = k
  · subst h
    rw [matMul_adj_diag (evalMat (charMat M) x) n i hi,
        show charScalarId M (n + 1) i i = charPoly M (n + 1) from if_pos rfl,
        eval_charPoly]
    exact det_congr (n + 1) (evalMat_charMat M x)
  · rw [matMul_adj_offdiag (evalMat (charMat M) x) n i k h hi hk,
        show charScalarId M (n + 1) i k = ([] : PolyZ) from if_neg h,
        show eval ([] : PolyZ) x = 0 from rfl]

/-- ★★★ **Polynomial adjugate identity** (the Cayley–Hamilton seed): the entries of
    `(X·I − M)·adj(X·I − M)` and of `χ_M·I` are equal integer polynomials. -/
theorem padj_identity (M : Nat → Nat → Int) (n i k : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    ∀ kk, coeff (pmatMul (n + 1) (charMat M) (padj n (charMat M)) i k) kk
        = coeff (charScalarId M (n + 1) i k) kk :=
  coeff_unique _ _ (padj_identity_eval M n i k hi hk)

end E213.Lib.Math.Linalg213.CharPolyAdj
