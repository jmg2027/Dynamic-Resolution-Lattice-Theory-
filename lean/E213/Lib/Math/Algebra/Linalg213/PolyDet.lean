import E213.Lib.Math.Algebra.Linalg213.DetN
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

namespace E213.Lib.Math.Algebra.Linalg213.PolyDet

open E213.Lib.Math.Algebra.Linalg213.DetN (det cofSum minor colShift altSign det_congr)
open E213.Lib.Math.PolyZ (PolyZ eval C addP scaleP mulP coeff eval_C eval_addP eval_scaleP eval_mulP
  degLe degLe_nil degLe_addP degLe_scaleP degLe_mulP degLe_mono
  coeff_addP coeff_scaleP coeff_mulP_single coeff_mulP_pair_succ coeff_eq_zero_of_degLe
  one_mul' mul_zero')

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

/-! ## §2 — the characteristic polynomial `χ_M = det(XI − M)` -/

/-- The **characteristic matrix** `X·I − M` as a polynomial matrix: the diagonal entries are
    `X − Mᵢᵢ = [−Mᵢᵢ, 1]`, the off-diagonal entries the constants `[−Mᵢⱼ]`. -/
def charMat (M : Nat → Nat → Int) : Nat → Nat → PolyZ :=
  fun i j => if i = j then [(- M i j), 1] else [(- M i j)]

/-- The **characteristic polynomial** `χ_M = det(X·I − M)` (an `N×N` determinant), as an
    actual integer-coefficient polynomial. -/
def charPoly (M : Nat → Nat → Int) (N : Nat) : PolyZ := pdet N (charMat M)

/-- Evaluating the characteristic matrix at `x` gives `x·I − M` pointwise. -/
theorem evalMat_charMat (M : Nat → Nat → Int) (x : Int) (i j : Nat) :
    evalMat (charMat M) x i j = (if i = j then x else 0) - M i j := by
  show eval (if i = j then [(- M i j), 1] else [(- M i j)]) x = (if i = j then x else 0) - M i j
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
    show (- M i j) + x * (1 + x * eval [] x) = x - M i j
    rw [Int.sub_eq_add_neg, show eval ([] : PolyZ) x = 0 from rfl,
        E213.Meta.Int213.mul_comm x 0, E213.Meta.Int213.zero_mul,
        E213.Meta.Int213.add_comm (1 : Int) 0, E213.Meta.Int213.zero_add,
        E213.Meta.Int213.mul_one, E213.Meta.Int213.add_comm (- M i j) x]
  · rw [if_neg h, if_neg h]
    show (- M i j) + x * eval [] x = 0 - M i j
    rw [Int.sub_eq_add_neg, show eval ([] : PolyZ) x = 0 from rfl,
        E213.Meta.Int213.mul_comm x 0, E213.Meta.Int213.zero_mul,
        E213.Meta.Int213.add_comm (- M i j) 0]

/-- ★ **The characteristic polynomial evaluates to `det(x·I − M)`** for every integer `x`. -/
theorem eval_charPoly (M : Nat → Nat → Int) (N : Nat) (x : Int) :
    eval (charPoly M N) x = det N (fun i j => (if i = j then x else 0) - M i j) := by
  rw [show charPoly M N = pdet N (charMat M) from rfl, eval_pdet N (charMat M) x]
  exact det_congr N (evalMat_charMat M x)

/-! ## §3 — the degree bound: `deg (pdet n A) ≤ n` for degree-`≤1` entries -/

/-- Cofactor-sum step of the degree bound: `deg (pcofSum (pdet n) A c) ≤ n+1`. -/
theorem degLe_pcofSum (n : Nat) (A : Nat → Nat → PolyZ) (hA : ∀ i j, degLe (A i j) 1)
    (ih : ∀ (B : Nat → Nat → PolyZ), (∀ i j, degLe (B i j) 1) → degLe (pdet n B) n) :
    ∀ (c : Nat), degLe (pcofSum (pdet n) A c) (n + 1)
  | 0     => degLe_nil _
  | c + 1 => by
    show degLe (addP (pcofSum (pdet n) A c)
      (scaleP (altSign c) (mulP (A 0 c) (pdet n (pminor A c))))) (n + 1)
    apply degLe_addP
    · exact degLe_pcofSum n A hA ih c
    · apply degLe_scaleP
      have hmul : degLe (mulP (A 0 c) (pdet n (pminor A c))) (1 + n) :=
        degLe_mulP (A 0 c) 1 (pdet n (pminor A c)) n (hA 0 c)
          (ih (pminor A c) (fun _ _ => hA _ _))
      rw [Nat.add_comm 1 n] at hmul
      exact hmul

/-- ★ **Degree bound**: `pdet` of an `n×n` matrix with degree-`≤1` entries has degree `≤ n`. -/
theorem degLe_pdet : ∀ (n : Nat) (A : Nat → Nat → PolyZ), (∀ i j, degLe (A i j) 1) →
    degLe (pdet n A) n
  | 0,     _, _  => by
    intro m hm
    cases m with
    | zero   => exact absurd hm (Nat.lt_irrefl 0)
    | succ _ => rfl
  | n + 1, A, hA => by
    show degLe (pcofSum (pdet n) A (n + 1)) (n + 1)
    exact degLe_pcofSum n A hA (fun B hB => degLe_pdet n B hB) (n + 1)

/-! ## §4 — monicity: `coeff (charPoly M N) N = 1` (the leading `Xᴺ` coefficient) -/

/-- Cofactor sum respects pointwise equality (given the inner determinant congruence). -/
theorem pcofSum_congr (n : Nat) {A A' : Nat → Nat → PolyZ}
    (hmin : ∀ c, pdet n (pminor A c) = pdet n (pminor A' c)) (h0 : ∀ c, A 0 c = A' 0 c) :
    ∀ (C : Nat), pcofSum (pdet n) A C = pcofSum (pdet n) A' C
  | 0     => rfl
  | C + 1 => by
    show addP (pcofSum (pdet n) A C) (scaleP (altSign C) (mulP (A 0 C) (pdet n (pminor A C))))
       = addP (pcofSum (pdet n) A' C) (scaleP (altSign C) (mulP (A' 0 C) (pdet n (pminor A' C))))
    rw [pcofSum_congr n hmin h0 C, h0 C, hmin C]

/-- `pdet` respects pointwise equality of polynomial matrices. -/
theorem pdet_congr : ∀ (n : Nat) {A A' : Nat → Nat → PolyZ}, (∀ i j, A i j = A' i j) →
    pdet n A = pdet n A'
  | 0,     _, _, _ => rfl
  | n + 1, A, A', h => by
    show pcofSum (pdet n) A (n + 1) = pcofSum (pdet n) A' (n + 1)
    exact pcofSum_congr n (fun c => pdet_congr n (fun i l => h (i + 1) (colShift c l)))
      (fun c => h 0 c) (n + 1)

/-- Each entry of the characteristic matrix has degree `≤ 1`. -/
theorem degLe_charMat (M : Nat → Nat → Int) (i j : Nat) : degLe (charMat M i j) 1 := by
  intro m hm
  by_cases h : i = j
  · rw [show charMat M i j = [(- M i j), 1] from if_pos h]
    cases m with
    | zero => exact absurd hm (Nat.not_lt_zero _)
    | succ m1 => cases m1 with
      | zero   => exact absurd hm (Nat.lt_irrefl 1)
      | succ _ => rfl
  · rw [show charMat M i j = [(- M i j)] from if_neg h]
    cases m with
    | zero   => exact absurd hm (Nat.not_lt_zero _)
    | succ _ => rfl

/-- The `(0,0)`-minor of `X·I − M` is the characteristic matrix of the shifted matrix. -/
theorem pminor_charMat_zero (M : Nat → Nat → Int) (i l : Nat) :
    pminor (charMat M) 0 i l = charMat (fun a b => M (a + 1) (b + 1)) i l := by
  show charMat M (i + 1) (colShift 0 l) = charMat (fun a b => M (a + 1) (b + 1)) i l
  rw [show colShift 0 l = l + 1 from rfl]
  by_cases h : i = l
  · rw [show charMat M (i + 1) (l + 1) = [(- M (i + 1) (l + 1)), 1] from if_pos (by rw [h]),
        show charMat (fun a b => M (a + 1) (b + 1)) i l = [(- M (i + 1) (l + 1)), 1] from if_pos h]
  · rw [show charMat M (i + 1) (l + 1) = [(- M (i + 1) (l + 1))] from
          if_neg (fun he => h (Nat.succ.inj he)),
        show charMat (fun a b => M (a + 1) (b + 1)) i l = [(- M (i + 1) (l + 1))] from if_neg h]

/-- The `c`-th cofactor term of `pdet (N+1) (charMat M)` has zero `X^{N+1}`-coefficient when `c ≠ 0`,
    and contributes the leading coefficient of the `(0,0)`-minor when `c = 0`. -/
theorem charMat_cofactor_coeff_top (M : Nat → Nat → Int) (N c : Nat) :
    coeff (scaleP (altSign c) (mulP (charMat M 0 c) (pdet N (pminor (charMat M) c)))) (N + 1)
      = (if c = 0 then coeff (pdet N (pminor (charMat M) 0)) N else 0) := by
  have hdeg : degLe (pdet N (pminor (charMat M) c)) N :=
    degLe_pdet N (pminor (charMat M) c) (fun _ _ => degLe_charMat M _ _)
  rw [coeff_scaleP]
  cases c with
  | zero =>
    rw [show charMat M 0 0 = [(- M 0 0), 1] from if_pos rfl, coeff_mulP_pair_succ,
        coeff_eq_zero_of_degLe hdeg (Nat.lt_succ_self N)]
    show altSign 0 * (- M 0 0 * 0 + 1 * coeff (pdet N (pminor (charMat M) 0)) N)
       = coeff (pdet N (pminor (charMat M) 0)) N
    rw [mul_zero', one_mul', show altSign 0 = 1 from rfl, one_mul',
        E213.Meta.Int213.zero_add]
  | succ c' =>
    rw [show charMat M 0 (c' + 1) = [(- M 0 (c' + 1))] from if_neg (fun he => Nat.noConfusion he),
        coeff_mulP_single, coeff_eq_zero_of_degLe hdeg (Nat.lt_succ_self N), mul_zero',
        if_neg (fun he => Nat.noConfusion he)]
    exact mul_zero' (altSign (c' + 1))

/-- The cofactor sum's `X^{N+1}`-coefficient = the `(0,0)`-minor's leading coefficient (only `c=0`
    contributes), for any positive number of columns. -/
theorem charMat_pcofSum_coeff_top (M : Nat → Nat → Int) (N : Nat) : ∀ (C : Nat),
    coeff (pcofSum (pdet N) (charMat M) (C + 1)) (N + 1)
      = coeff (pdet N (pminor (charMat M) 0)) N
  | 0     => by
    show coeff (addP (pcofSum (pdet N) (charMat M) 0)
      (scaleP (altSign 0) (mulP (charMat M 0 0) (pdet N (pminor (charMat M) 0))))) (N + 1) = _
    rw [coeff_addP, show pcofSum (pdet N) (charMat M) 0 = ([] : PolyZ) from rfl,
        show coeff ([] : PolyZ) (N + 1) = 0 from rfl, E213.Meta.Int213.zero_add,
        charMat_cofactor_coeff_top M N 0, if_pos rfl]
  | C + 1 => by
    show coeff (addP (pcofSum (pdet N) (charMat M) (C + 1))
      (scaleP (altSign (C + 1)) (mulP (charMat M 0 (C + 1)) (pdet N (pminor (charMat M) (C + 1))))))
        (N + 1) = _
    rw [coeff_addP, charMat_pcofSum_coeff_top M N C, charMat_cofactor_coeff_top M N (C + 1),
        if_neg (fun he => Nat.noConfusion he), E213.Meta.Int213.add_comm,
        E213.Meta.Int213.zero_add]

/-- ★★ **The characteristic polynomial is monic**: `coeff (charPoly M N) N = 1`. -/
theorem charPoly_monic : ∀ (N : Nat) (M : Nat → Nat → Int), coeff (charPoly M N) N = 1
  | 0,     _ => rfl
  | N + 1, M => by
    show coeff (pcofSum (pdet N) (charMat M) (N + 1)) (N + 1) = 1
    rw [charMat_pcofSum_coeff_top M N N,
        pdet_congr N (pminor_charMat_zero M)]
    exact charPoly_monic N (fun a b => M (a + 1) (b + 1))

end E213.Lib.Math.Algebra.Linalg213.PolyDet
