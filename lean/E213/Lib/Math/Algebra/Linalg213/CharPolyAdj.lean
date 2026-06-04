import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.PolyDet
import E213.Lib.Math.Algebra.Linalg213.CayleyHamilton

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

namespace E213.Lib.Math.Algebra.Linalg213.CharPolyAdj

open E213.Lib.Math.Algebra.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (map_eq_of_mem map_map' sumZ_map_add sumZ_map_smul lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.DetN (det altSign colShift det_congr)
open E213.Lib.Math.Algebra.Linalg213.Laplace
  (matMul adj minorAt matMul_adj_diag matMul_adj_offdiag sumZ_append map_append')
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton
  (sumZ_iota_delta_lt sumZ_map_neg sumZ_map_zero sumZ_singleton sumZ_swap sumZ_map_smul_right
   matMul_assoc matPow matId matMul_id_left matMul_id_right matMul_congr_bd matPow_succ_right)
open E213.Lib.Math.Algebra.Linalg213.PolyDet
  (pdet evalMat eval_pdet charMat charPoly eval_charPoly evalMat_charMat degLe_pdet)
open E213.Lib.Math.Algebra.PolyZ
  (PolyZ eval addP mulP scaleP coeff eval_addP eval_mulP eval_scaleP coeff_unique
   coeff_addP coeff_mulP_single coeff_mulP_pair_zero coeff_mulP_pair_succ one_mul' add_zero'
   coeff_nil degLe coeff_scaleP coeff_eq_zero_of_degLe mul_zero')

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

/-! ## §4 — the Cayley–Hamilton coefficient relations -/

/-- `coeff` of a `PolyZ` matrix product = the `Int` sum of the entry-product coefficients. -/
theorem coeff_pmatMul (n : Nat) (A B : Nat → Nat → PolyZ) (i k kk : Nat) :
    coeff (pmatMul n A B i k) kk = sumZ ((iota n).map (fun j => coeff (mulP (A i j) (B j k)) kk)) := by
  show coeff (psumZ ((iota n).map (fun j => mulP (A i j) (B j k)))) kk = _
  rw [show ∀ (L : List PolyZ), coeff (psumZ L) kk = sumZ (L.map (fun p => coeff p kk)) from
        (fun L => by
          induction L with
          | nil => rfl
          | cons p ps ih =>
            show coeff (addP p (psumZ ps)) kk = coeff p kk + sumZ (ps.map (fun p => coeff p kk))
            rw [coeff_addP, ih]),
      map_map' (fun j => mulP (A i j) (B j k)) (fun p => coeff p kk)]

/-- `coeff` of `χ_M·I` (the scalar matrix) at entry `(i,k)`. -/
theorem coeff_charScalarId (M : Nat → Nat → Int) (N i k kk : Nat) :
    coeff (charScalarId M N i k) kk = if i = k then coeff (charPoly M N) kk else 0 := by
  by_cases h : i = k
  · rw [show charScalarId M N i k = charPoly M N from if_pos h, if_pos h]
  · rw [show charScalarId M N i k = ([] : PolyZ) from if_neg h, if_neg h, coeff_nil]

/-- ★★ **CH relation at constant order**: `−(M·B₀) = c₀·I` (entry-wise).  Here
    `Bₖ(j,k) = coeff (adj(X·I−M)) k`, `cₖ = coeff χ_M k`. -/
theorem cayley_rel_zero (M : Nat → Nat → Int) (n i k : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    sumZ ((iota (n + 1)).map (fun j => (- M i j) * coeff (padj n (charMat M) j k) 0))
      = (if i = k then coeff (charPoly M (n + 1)) 0 else 0) := by
  rw [← coeff_charScalarId, ← padj_identity M n i k hi hk 0, coeff_pmatMul]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro j _
  by_cases h : i = j
  · rw [show charMat M i j = [(- M i j), 1] from if_pos h]
    exact (coeff_mulP_pair_zero (- M i j) 1 (padj n (charMat M) j k)).symm
  · rw [show charMat M i j = [(- M i j)] from if_neg h]
    exact (coeff_mulP_single (- M i j) (padj n (charMat M) j k) 0).symm

/-- ★★ **CH relation at order `m+1`**: `Bₘ − M·B_{m+1} = c_{m+1}·I` (entry-wise). -/
theorem cayley_rel_succ (M : Nat → Nat → Int) (n i k m : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    sumZ ((iota (n + 1)).map (fun j => (- M i j) * coeff (padj n (charMat M) j k) (m + 1)))
        + coeff (padj n (charMat M) i k) m
      = (if i = k then coeff (charPoly M (n + 1)) (m + 1) else 0) := by
  rw [← coeff_charScalarId, ← padj_identity M n i k hi hk (m + 1), coeff_pmatMul,
      map_eq_of_mem (fun j => coeff (mulP (charMat M i j) (padj n (charMat M) j k)) (m + 1))
        (fun j => (- M i j) * coeff (padj n (charMat M) j k) (m + 1)
                  + (if i = j then coeff (padj n (charMat M) j k) m else 0))
        (fun j _ => by
          show coeff (mulP (charMat M i j) (padj n (charMat M) j k)) (m + 1)
             = (- M i j) * coeff (padj n (charMat M) j k) (m + 1)
               + (if i = j then coeff (padj n (charMat M) j k) m else 0)
          by_cases h : i = j
          · rw [show charMat M i j = [(- M i j), 1] from if_pos h, coeff_mulP_pair_succ,
                if_pos h, one_mul']
          · rw [show charMat M i j = [(- M i j)] from if_neg h, coeff_mulP_single, if_neg h,
                add_zero']),
      sumZ_map_add,
      sumZ_iota_delta_lt (fun j => coeff (padj n (charMat M) j k) m) i (n + 1) hi]

/-! ## §5 — the top adjugate coefficient vanishes (`B_{n+1} = 0`) -/

/-- Each entry of the characteristic matrix has degree `≤ 1`. -/
theorem degLe_charMat (M : Nat → Nat → Int) (i j : Nat) : degLe (charMat M i j) 1 := by
  intro m hm
  by_cases h : i = j
  · rw [show charMat M i j = [(- M i j), 1] from if_pos h]
    cases m with
    | zero => exact absurd hm (Nat.not_lt_zero _)
    | succ m1 =>
      cases m1 with
      | zero   => exact absurd hm (Nat.lt_irrefl 1)
      | succ _ => rfl
  · rw [show charMat M i j = [(- M i j)] from if_neg h]
    cases m with
    | zero   => exact absurd hm (Nat.not_lt_zero _)
    | succ _ => rfl

/-- ★ **The degree-`(n+1)` coefficient of the adjugate vanishes** (`adj(X·I−M)` has degree `≤ n`).
    This is the telescoping's vanishing boundary term. -/
theorem padj_coeff_top_zero (M : Nat → Nat → Int) (n i j : Nat) :
    coeff (padj n (charMat M) i j) (n + 1) = 0 := by
  show coeff (scaleP (altSign (j + i)) (pdet n (pminorAt j i (charMat M)))) (n + 1) = 0
  rw [coeff_scaleP,
      coeff_eq_zero_of_degLe
        (degLe_pdet n (pminorAt j i (charMat M)) (fun _ _ => degLe_charMat M _ _))
        (Nat.lt_succ_self n),
      mul_zero']

/-! ## §6 — the relations as matrix equations (`B_{m-1} − M·B_m = c_m·I`) -/

/-- The adjugate coefficient matrix `B_m(i,j) = coeff (adj(X·I−M)) m`. -/
def Bm (M : Nat → Nat → Int) (n m : Nat) : Nat → Nat → Int :=
  fun i j => coeff (padj n (charMat M) i j) m

/-- The characteristic-polynomial coefficient `c_m`. -/
def cm (M : Nat → Nat → Int) (n m : Nat) : Int := coeff (charPoly M (n + 1)) m

/-- `M·B` written via the signed sum that the CH relations produce. -/
theorem matMul_eq_neg_sumNeg (n : Nat) (M B : Nat → Nat → Int) (i k : Nat) :
    matMul (n + 1) M B i k = - sumZ ((iota (n + 1)).map (fun j => (- M i j) * B j k)) := by
  show sumZ ((iota (n + 1)).map (fun j => M i j * B j k))
     = - sumZ ((iota (n + 1)).map (fun j => (- M i j) * B j k))
  rw [← sumZ_map_neg (fun j => (- M i j) * B j k)]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro j _
  rw [E213.Meta.Int213.neg_mul, Int.neg_neg]

/-- ★★ **CH relation at order 0 (matrix form)**: `M·B₀ = −c₀·I`. -/
theorem matMul_Bm_zero (M : Nat → Nat → Int) (n i k : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    matMul (n + 1) M (Bm M n 0) i k = - (if i = k then cm M n 0 else 0) := by
  rw [matMul_eq_neg_sumNeg]
  show - sumZ ((iota (n + 1)).map (fun j => (- M i j) * coeff (padj n (charMat M) j k) 0))
     = - (if i = k then coeff (charPoly M (n + 1)) 0 else 0)
  rw [cayley_rel_zero M n i k hi hk]

/-- ★★ **CH relation at order `m+1` (matrix form)**: `M·B_{m+1} = Bₘ − c_{m+1}·I`. -/
theorem matMul_Bm_succ (M : Nat → Nat → Int) (n i k m : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    matMul (n + 1) M (Bm M n (m + 1)) i k
      = Bm M n m i k - (if i = k then cm M n (m + 1) else 0) := by
  rw [matMul_eq_neg_sumNeg]
  have h := cayley_rel_succ M n i k m hi hk
  show - sumZ ((iota (n + 1)).map (fun j => (- M i j) * coeff (padj n (charMat M) j k) (m + 1)))
     = coeff (padj n (charMat M) i k) m
       - (if i = k then coeff (charPoly M (n + 1)) (m + 1) else 0)
  rw [Int.sub_eq_add_neg, ← h]
  ring_intZ

/-! ## §7 — the telescoping ⟹ integer Cayley–Hamilton `χ_M(M) = 0` -/

/-- `sumZ` of a pointwise difference. -/
theorem sumZ_map_sub {α : Type} (f g : α → Int) (L : List α) :
    sumZ (L.map (fun a => f a - g a)) = sumZ (L.map f) - sumZ (L.map g) := by
  show sumZ (L.map (fun a => f a + -(g a))) = sumZ (L.map f) - sumZ (L.map g)
  rw [E213.Lib.Math.Algebra.Linalg213.PermClosure.sumZ_map_add f (fun a => -(g a)), sumZ_map_neg g,
      Int.sub_eq_add_neg]

/-- Partial characteristic sum `Σ_{m=0}^{N} c_m·(Mᵐ)_{ik}`. -/
def charSum (M : Nat → Nat → Int) (n N i k : Nat) : Int :=
  sumZ ((iota (N + 1)).map (fun m => cm M n m * matPow (n + 1) M m i k))

theorem charSum_zero (M : Nat → Nat → Int) (n i k : Nat) :
    charSum M n 0 i k = cm M n 0 * matPow (n + 1) M 0 i k := by
  show sumZ ((iota 1).map (fun m => cm M n m * matPow (n + 1) M m i k))
     = cm M n 0 * matPow (n + 1) M 0 i k
  rw [show (iota 1).map (fun m => cm M n m * matPow (n + 1) M m i k)
        = [cm M n 0 * matPow (n + 1) M 0 i k] from rfl, sumZ_singleton]

theorem charSum_succ (M : Nat → Nat → Int) (n N i k : Nat) :
    charSum M n (N + 1) i k
      = charSum M n N i k + cm M n (N + 1) * matPow (n + 1) M (N + 1) i k := by
  show sumZ ((iota (N + 2)).map (fun m => cm M n m * matPow (n + 1) M m i k))
     = sumZ ((iota (N + 1)).map (fun m => cm M n m * matPow (n + 1) M m i k))
       + cm M n (N + 1) * matPow (n + 1) M (N + 1) i k
  rw [show iota (N + 2) = iota (N + 1) ++ [N + 1] from rfl, map_append', sumZ_append,
      show ([N + 1] : List Nat).map (fun m => cm M n m * matPow (n + 1) M m i k)
        = [cm M n (N + 1) * matPow (n + 1) M (N + 1) i k] from rfl, sumZ_singleton]

/-- The telescoping step: `Mᴺ⁺²·B_{N+1} = Mᴺ⁺¹·B_N − c_{N+1}·Mᴺ⁺¹` (entry-wise). -/
theorem tele_step (M : Nat → Nat → Int) (n N i k : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    matMul (n + 1) (matPow (n + 1) M (N + 2)) (Bm M n (N + 1)) i k
      = matMul (n + 1) (matPow (n + 1) M (N + 1)) (Bm M n N) i k
        - cm M n (N + 1) * matPow (n + 1) M (N + 1) i k := by
  rw [matMul_congr_bd (n + 1) (matPow (n + 1) M (N + 2))
        (matMul (n + 1) (matPow (n + 1) M (N + 1)) M) (Bm M n (N + 1)) (Bm M n (N + 1)) i k
        (fun j hj => (matPow_succ_right n M (N + 1) i j hi hj).symm) (fun _ _ => rfl),
      ← matMul_assoc,
      matMul_congr_bd (n + 1) (matPow (n + 1) M (N + 1)) (matPow (n + 1) M (N + 1))
        (matMul (n + 1) M (Bm M n (N + 1)))
        (fun j k' => Bm M n N j k' - (if j = k' then cm M n (N + 1) else 0)) i k
        (fun _ _ => rfl) (fun j hj => matMul_Bm_succ M n j k N hj hk)]
  show sumZ ((iota (n + 1)).map
        (fun j => matPow (n + 1) M (N + 1) i j
          * (Bm M n N j k - (if j = k then cm M n (N + 1) else 0))))
     = matMul (n + 1) (matPow (n + 1) M (N + 1)) (Bm M n N) i k
       - cm M n (N + 1) * matPow (n + 1) M (N + 1) i k
  rw [map_eq_of_mem
        (fun j => matPow (n + 1) M (N + 1) i j
          * (Bm M n N j k - (if j = k then cm M n (N + 1) else 0)))
        (fun j => matPow (n + 1) M (N + 1) i j * Bm M n N j k
          - matPow (n + 1) M (N + 1) i j * (if j = k then cm M n (N + 1) else 0))
        (fun j _ => by
          show matPow (n + 1) M (N + 1) i j * (Bm M n N j k - (if j = k then cm M n (N + 1) else 0))
             = matPow (n + 1) M (N + 1) i j * Bm M n N j k
               - matPow (n + 1) M (N + 1) i j * (if j = k then cm M n (N + 1) else 0)
          ring_intZ),
      sumZ_map_sub (fun j => matPow (n + 1) M (N + 1) i j * Bm M n N j k)
        (fun j => matPow (n + 1) M (N + 1) i j * (if j = k then cm M n (N + 1) else 0))]
  have hY : sumZ ((iota (n + 1)).map
        (fun j => matPow (n + 1) M (N + 1) i j * (if j = k then cm M n (N + 1) else 0)))
      = cm M n (N + 1) * matPow (n + 1) M (N + 1) i k := by
    rw [map_eq_of_mem
          (fun j => matPow (n + 1) M (N + 1) i j * (if j = k then cm M n (N + 1) else 0))
          (fun j => if k = j then cm M n (N + 1) * matPow (n + 1) M (N + 1) i k else 0)
          (fun j _ => by
            show matPow (n + 1) M (N + 1) i j * (if j = k then cm M n (N + 1) else 0)
               = if k = j then cm M n (N + 1) * matPow (n + 1) M (N + 1) i k else 0
            by_cases h : j = k
            · rw [if_pos h, if_pos h.symm, h]; ring_intZ
            · rw [if_neg h, if_neg (fun he => h he.symm), mul_zero']),
        sumZ_iota_delta_lt (fun _ => cm M n (N + 1) * matPow (n + 1) M (N + 1) i k) k (n + 1) hk]
  rw [hY]
  rfl

/-- ★ **The telescoping identity**: `Σ_{m=0}^{N} c_m·Mᵐ = − Mᴺ⁺¹·B_N` (entry-wise). -/
theorem telescope (M : Nat → Nat → Int) (n : Nat) :
    ∀ (N i k : Nat), i < n + 1 → k < n + 1 →
      charSum M n N i k = - matMul (n + 1) (matPow (n + 1) M (N + 1)) (Bm M n N) i k
  | 0,     i, k, hi, hk => by
    rw [charSum_zero,
        matMul_congr_bd (n + 1) (matPow (n + 1) M 1) M (Bm M n 0) (Bm M n 0) i k
          (fun j hj => matMul_id_right (n + 1) M i j hj) (fun _ _ => rfl),
        matMul_Bm_zero M n i k hi hk, Int.neg_neg]
    show cm M n 0 * matId i k = if i = k then cm M n 0 else 0
    by_cases h : i = k
    · rw [if_pos h]; show cm M n 0 * (if i = k then 1 else 0) = cm M n 0
      rw [if_pos h, E213.Meta.Int213.mul_one]
    · rw [if_neg h]; show cm M n 0 * (if i = k then 1 else 0) = 0
      rw [if_neg h, mul_zero']
  | N + 1, i, k, hi, hk => by
    rw [charSum_succ, telescope M n N i k hi hk, tele_step M n N i k hi hk]
    ring_intZ

/-- ★★★ **Integer Cayley–Hamilton** (entry-wise): the characteristic polynomial annihilates
    its own matrix, `χ_M(M) = 0`, i.e. `Σ_{m=0}^{n+1} c_m·(Mᵐ)_{ik} = 0`.  ∅-axiom. -/
theorem cayley_hamilton (M : Nat → Nat → Int) (n i k : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    sumZ ((iota (n + 2)).map (fun m => coeff (charPoly M (n + 1)) m * matPow (n + 1) M m i k)) = 0 := by
  show charSum M n (n + 1) i k = 0
  rw [telescope M n (n + 1) i k hi hk]
  have hzero : matMul (n + 1) (matPow (n + 1) M (n + 2)) (Bm M n (n + 1)) i k = 0 := by
    show sumZ ((iota (n + 1)).map
      (fun j => matPow (n + 1) M (n + 2) i j * Bm M n (n + 1) j k)) = 0
    rw [map_eq_of_mem
          (fun j => matPow (n + 1) M (n + 2) i j * Bm M n (n + 1) j k) (fun _ => 0)
          (fun j _ => by
            show matPow (n + 1) M (n + 2) i j * Bm M n (n + 1) j k = 0
            rw [show Bm M n (n + 1) j k = 0 from padj_coeff_top_zero M n j k, mul_zero']),
        sumZ_map_zero]
  rw [hzero, Int.neg_zero]

/-! ## §8 — the Cayley–Hamilton recurrence bridge (vector recurrence ⟹ scalar recurrence) -/

/-- A vector sequence `w` evolving by `w(n+1) = M·w(n)` satisfies `w(n+m) = Mᵐ·w(n)`
    (component-wise, over the index range `< N+1`). -/
theorem wPow (M : Nat → Nat → Int) (w : Nat → Nat → Int) (N : Nat)
    (hrec : ∀ n j, j < N + 1 → w (n + 1) j = sumZ ((iota (N + 1)).map (fun k => M j k * w n k))) :
    ∀ (m n j : Nat), j < N + 1 →
      w (n + m) j = sumZ ((iota (N + 1)).map (fun k => matPow (N + 1) M m j k * w n k))
  | 0,     n, j, hj => by
    show w n j = sumZ ((iota (N + 1)).map (fun k => matId j k * w n k))
    rw [map_eq_of_mem (fun k => matId j k * w n k) (fun k => if j = k then w n k else 0)
          (fun k _ => by
            show (if j = k then (1 : Int) else 0) * w n k = if j = k then w n k else 0
            by_cases h : j = k
            · rw [if_pos h, if_pos h]; exact one_mul' (w n k)
            · rw [if_neg h, if_neg h]; exact E213.Meta.Int213.zero_mul (w n k)),
        sumZ_iota_delta_lt (fun k => w n k) j (N + 1) hj]
  | m + 1, n, j, hj => by
    show w (n + m + 1) j = sumZ ((iota (N + 1)).map (fun l => matPow (N + 1) M (m + 1) j l * w n l))
    rw [hrec (n + m) j hj,
        map_eq_of_mem (fun k => M j k * w (n + m) k)
          (fun k => sumZ ((iota (N + 1)).map (fun l => M j k * (matPow (N + 1) M m k l * w n l))))
          (fun k hk => by
            show M j k * w (n + m) k
               = sumZ ((iota (N + 1)).map (fun l => M j k * (matPow (N + 1) M m k l * w n l)))
            rw [wPow M w N hrec m n k (lt_of_mem_iota hk), ← sumZ_map_smul]),
        sumZ_swap (fun k l => M j k * (matPow (N + 1) M m k l * w n l)),
        map_eq_of_mem
          (fun l => sumZ ((iota (N + 1)).map (fun k => M j k * (matPow (N + 1) M m k l * w n l))))
          (fun l => matPow (N + 1) M (m + 1) j l * w n l)
          (fun l _ => by
            show sumZ ((iota (N + 1)).map (fun k => M j k * (matPow (N + 1) M m k l * w n l)))
               = matPow (N + 1) M (m + 1) j l * w n l
            rw [map_eq_of_mem (fun k => M j k * (matPow (N + 1) M m k l * w n l))
                  (fun k => M j k * matPow (N + 1) M m k l * w n l)
                  (fun k _ => (E213.Meta.Int213.mul_assoc _ _ _).symm),
                ← sumZ_map_smul_right]
            rfl)]

/-- ★★★ **The Cayley–Hamilton recurrence**: if `w(n+1) = M·w(n)` then every component of `w`
    satisfies the monic order-`(N+1)` recurrence with the characteristic-polynomial coefficients. -/
theorem ch_recurrence (M : Nat → Nat → Int) (w : Nat → Nat → Int) (N : Nat)
    (hrec : ∀ n j, j < N + 1 → w (n + 1) j = sumZ ((iota (N + 1)).map (fun k => M j k * w n k)))
    (n j : Nat) (hj : j < N + 1) :
    sumZ ((iota (N + 2)).map (fun m => coeff (charPoly M (N + 1)) m * w (n + m) j)) = 0 := by
  rw [map_eq_of_mem (fun m => coeff (charPoly M (N + 1)) m * w (n + m) j)
        (fun m => sumZ ((iota (N + 1)).map
          (fun k => coeff (charPoly M (N + 1)) m * (matPow (N + 1) M m j k * w n k))))
        (fun m _ => by
          show coeff (charPoly M (N + 1)) m * w (n + m) j
             = sumZ ((iota (N + 1)).map
                (fun k => coeff (charPoly M (N + 1)) m * (matPow (N + 1) M m j k * w n k)))
          rw [wPow M w N hrec m n j hj, ← sumZ_map_smul]),
      sumZ_swap (fun m k => coeff (charPoly M (N + 1)) m * (matPow (N + 1) M m j k * w n k))]
  rw [map_eq_of_mem
        (fun k => sumZ ((iota (N + 2)).map
          (fun m => coeff (charPoly M (N + 1)) m * (matPow (N + 1) M m j k * w n k))))
        (fun _ => 0)
        (fun k hk => by
          show sumZ ((iota (N + 2)).map
            (fun m => coeff (charPoly M (N + 1)) m * (matPow (N + 1) M m j k * w n k))) = 0
          rw [map_eq_of_mem
                (fun m => coeff (charPoly M (N + 1)) m * (matPow (N + 1) M m j k * w n k))
                (fun m => coeff (charPoly M (N + 1)) m * matPow (N + 1) M m j k * w n k)
                (fun m _ => (E213.Meta.Int213.mul_assoc _ _ _).symm),
              ← sumZ_map_smul_right, cayley_hamilton M N j k hj (lt_of_mem_iota hk),
              E213.Meta.Int213.zero_mul]),
      sumZ_map_zero]

end E213.Lib.Math.Algebra.Linalg213.CharPolyAdj
