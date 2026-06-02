import E213.Meta.Nat.PolyNatM
import E213.Meta.Int213.Core

/-!
# `PolyIntM` — a ∅-axiom reflection prover for *multivariate* `Int` polynomial identities

The `ℤ` companion of `Meta/Nat/PolyNatM` (and the `k`-variable generalization of the bivariate
`Meta/Int213/PolyInt2`).  Reuses PolyNatM's coefficient-agnostic monomial helpers (`zipAdd`,
`monoBeq`, `eq_of_monoBeq`, `monoLt`, `varMono`); adds the `ℤ`-coefficient layer with negation
and — crucially over `ℤ` — **zero-coefficient dropping** in `insertAddZ`, so signed
cancellation (`(a−b)·(a+b) = a²−b²`, `a−b+b = a`) normalises correctly.  Powers use a
repeated-multiplication `powInt` (Lean-core `Int` `^` lemmas are absent / `propext`-laden).

All zero-axiom.
-/

namespace E213.Meta.Int213.PolyIntM

open E213.Meta.Nat.PolyNatM (zipAdd monoBeq eq_of_monoBeq monoLt)
open E213.Meta.Int213
  (add_comm add_assoc mul_comm mul_assoc mul_left_comm add_mul mul_add mul_one zero_mul
   neg_mul mul_neg add_neg_cancel zero_add neg_add)

/-! ## §0 — local PURE Int helpers (the missing ring corners) -/

theorem one_mulZ (a : Int) : 1 * a = a := by rw [mul_comm, mul_one]
theorem mul_zeroZ (a : Int) : a * 0 = 0 := by rw [mul_comm, zero_mul]
theorem neg_zeroZ : -(0 : Int) = 0 := (zero_add (-0)).symm.trans (add_neg_cancel 0)

/-- A Boolean "is zero" test on `Int` (for the zero-drop), with its soundness. -/
def isZeroZ : Int → Bool
  | Int.ofNat 0 => true
  | _           => false

theorem isZeroZ_eq : ∀ {c : Int}, isZeroZ c = true → c = 0
  | Int.ofNat 0,     _ => rfl
  | Int.ofNat (_+1), h => Bool.noConfusion h
  | Int.negSucc _,   h => Bool.noConfusion h

/-! ## §1 — monomials over an `Int` environment -/

/-- Repeated-multiplication power on `Int` (no core `^`). -/
def powInt (x : Int) : Nat → Int
  | 0     => 1
  | k + 1 => powInt x k * x

theorem powInt_add (x : Int) (a : Nat) : ∀ b, powInt x (a + b) = powInt x a * powInt x b
  | 0     => by show powInt x a = powInt x a * 1; rw [mul_one]
  | b + 1 => by
      show powInt x (a + b) * x = powInt x a * (powInt x b * x)
      rw [powInt_add x a b, mul_assoc]

/-- Evaluate a monomial (exponent vector) at an `Int` environment. -/
def monoEvalZ : List Nat → List Int → Int
  | [],      _   => 1
  | e :: es, env => powInt (env.headD 0) e * monoEvalZ es env.tail

/-- `(X·Y)·(Z·W) = (X·Z)·(Y·W)` over `Int` (PURE Int213 mul-rearrange). -/
private theorem mulZ4 (X Y Z W : Int) : (X * Y) * (Z * W) = (X * Z) * (Y * W) := by
  rw [mul_assoc X Y (Z * W), mul_left_comm Y Z W, ← mul_assoc X Z (Y * W)]

theorem zipAdd_evalZ : ∀ a b env, monoEvalZ (zipAdd a b) env = monoEvalZ a env * monoEvalZ b env
  | [],      b,      env => by show monoEvalZ b env = 1 * monoEvalZ b env; rw [one_mulZ]
  | a :: as, [],     env => by show monoEvalZ (a::as) env = monoEvalZ (a::as) env * 1; rw [mul_one]
  | a :: as, b :: bs, env => by
      show powInt (env.headD 0) (a + b) * monoEvalZ (zipAdd as bs) env.tail
         = (powInt (env.headD 0) a * monoEvalZ as env.tail)
           * (powInt (env.headD 0) b * monoEvalZ bs env.tail)
      rw [powInt_add, zipAdd_evalZ as bs env.tail]
      exact mulZ4 _ _ _ _

/-! ## §2 — `Int`-coefficient normal form, with zero-drop -/

/-- Evaluate a normal form. -/
def nfEvalZ : List (List Nat × Int) → List Int → Int
  | [],             _   => 0
  | (m, c) :: rest, env => c * monoEvalZ m env + nfEvalZ rest env

/-- Insert `(m, c)` into a sorted normal form, merging equal monomials and **dropping**
    entries whose coefficient becomes `0` (needed over `ℤ` for cancellation). -/
def insertAddZ (m : List Nat) (c : Int) : List (List Nat × Int) → List (List Nat × Int)
  | []             => [(m, c)]
  | (m', c') :: rest =>
      if monoBeq m m' then
        (if isZeroZ (c + c') then rest else (m', c + c') :: rest)
      else if monoLt m m' then (m, c) :: (m', c') :: rest
      else (m', c') :: insertAddZ m c rest

theorem insertAddZ_eval (m : List Nat) (c : Int) :
    ∀ nf env, nfEvalZ (insertAddZ m c nf) env = c * monoEvalZ m env + nfEvalZ nf env
  | [],              _   => rfl
  | (m', c') :: rest, env => by
      show nfEvalZ (if monoBeq m m' then
                      (if isZeroZ (c + c') then rest else (m', c + c') :: rest)
                    else if monoLt m m' then ((m, c) :: (m', c') :: rest)
                    else ((m', c') :: insertAddZ m c rest)) env
         = c * monoEvalZ m env + (c' * monoEvalZ m' env + nfEvalZ rest env)
      cases hb : monoBeq m m' with
      | true =>
          have hmm : m = m' := eq_of_monoBeq hb
          subst hmm
          cases hz : isZeroZ (c + c') with
          | true =>
              have hc0 : c + c' = 0 := isZeroZ_eq hz
              show nfEvalZ rest env = c * monoEvalZ m env + (c' * monoEvalZ m env + nfEvalZ rest env)
              rw [← add_assoc (c * monoEvalZ m env) (c' * monoEvalZ m env) (nfEvalZ rest env),
                  ← add_mul c c' (monoEvalZ m env), hc0, zero_mul, zero_add]
          | false =>
              show (c + c') * monoEvalZ m env + nfEvalZ rest env
                 = c * monoEvalZ m env + (c' * monoEvalZ m env + nfEvalZ rest env)
              rw [add_mul c c' (monoEvalZ m env), add_assoc]
      | false =>
          cases hl : monoLt m m' with
          | true => rfl
          | false =>
              show c' * monoEvalZ m' env + nfEvalZ (insertAddZ m c rest) env
                 = c * monoEvalZ m env + (c' * monoEvalZ m' env + nfEvalZ rest env)
              rw [insertAddZ_eval m c rest env, ← add_assoc, ← add_assoc,
                  add_comm (c' * monoEvalZ m' env) (c * monoEvalZ m env)]

/-- Sum of two normal forms. -/
def addNFZ : List (List Nat × Int) → List (List Nat × Int) → List (List Nat × Int)
  | [],             q => q
  | (m, c) :: rest, q => insertAddZ m c (addNFZ rest q)

theorem addNFZ_eval : ∀ p q env, nfEvalZ (addNFZ p q) env = nfEvalZ p env + nfEvalZ q env
  | [],             q, env => by show nfEvalZ q env = 0 + nfEvalZ q env; rw [zero_add]
  | (m, c) :: rest, q, env => by
      show nfEvalZ (insertAddZ m c (addNFZ rest q)) env
         = c * monoEvalZ m env + nfEvalZ rest env + nfEvalZ q env
      rw [insertAddZ_eval m c (addNFZ rest q) env, addNFZ_eval rest q env, add_assoc]

/-- Negate a normal form. -/
def negNFZ : List (List Nat × Int) → List (List Nat × Int)
  | []             => []
  | (m, c) :: rest => (m, -c) :: negNFZ rest

theorem negNFZ_eval : ∀ p env, nfEvalZ (negNFZ p) env = -(nfEvalZ p env)
  | [],             env => by show (0:Int) = -(0:Int); rw [neg_zeroZ]
  | (m, c) :: rest, env => by
      show (-c) * monoEvalZ m env + nfEvalZ (negNFZ rest) env = -(c * monoEvalZ m env + nfEvalZ rest env)
      rw [negNFZ_eval rest env, neg_mul c (monoEvalZ m env), neg_add (c * monoEvalZ m env) (nfEvalZ rest env)]

/-- Multiply a normal form by a single monomial-coefficient. -/
def scaleNFZ (m0 : List Nat) (c0 : Int) : List (List Nat × Int) → List (List Nat × Int)
  | []             => []
  | (m, c) :: rest => insertAddZ (zipAdd m0 m) (c0 * c) (scaleNFZ m0 c0 rest)

theorem scaleNFZ_eval (m0 : List Nat) (c0 : Int) :
    ∀ q env, nfEvalZ (scaleNFZ m0 c0 q) env = (c0 * monoEvalZ m0 env) * nfEvalZ q env
  | [],             env => by show (0:Int) = (c0 * monoEvalZ m0 env) * 0; rw [mul_zeroZ]
  | (m, c) :: rest, env => by
      show nfEvalZ (insertAddZ (zipAdd m0 m) (c0 * c) (scaleNFZ m0 c0 rest)) env
         = (c0 * monoEvalZ m0 env) * (c * monoEvalZ m env + nfEvalZ rest env)
      rw [insertAddZ_eval (zipAdd m0 m) (c0 * c) (scaleNFZ m0 c0 rest) env,
          scaleNFZ_eval m0 c0 rest env, zipAdd_evalZ m0 m env,
          mul_add (c0 * monoEvalZ m0 env) (c * monoEvalZ m env) (nfEvalZ rest env)]
      rw [mulZ4 c0 c (monoEvalZ m0 env) (monoEvalZ m env)]

/-- Product of two normal forms. -/
def mulNFZ : List (List Nat × Int) → List (List Nat × Int) → List (List Nat × Int)
  | [],             _ => []
  | (m, c) :: rest, q => addNFZ (scaleNFZ m c q) (mulNFZ rest q)

theorem mulNFZ_eval : ∀ p q env, nfEvalZ (mulNFZ p q) env = nfEvalZ p env * nfEvalZ q env
  | [],             q, env => by show (0:Int) = 0 * nfEvalZ q env; rw [zero_mul]
  | (m, c) :: rest, q, env => by
      show nfEvalZ (addNFZ (scaleNFZ m c q) (mulNFZ rest q)) env
         = (c * monoEvalZ m env + nfEvalZ rest env) * nfEvalZ q env
      rw [addNFZ_eval (scaleNFZ m c q) (mulNFZ rest q) env, scaleNFZ_eval m c q env,
          mulNFZ_eval rest q env, add_mul (c * monoEvalZ m env) (nfEvalZ rest env) (nfEvalZ q env)]

/-! ## §3 — expression type, normal form, driver -/

/-- A multivariate `Int` polynomial expression. -/
inductive PE where
  | var : Nat → PE
  | C   : Int → PE
  | add : PE → PE → PE
  | mul : PE → PE → PE
  | neg : PE → PE

def PE.eval : PE → List Int → Int
  | .var i,   env => env.getD i 0
  | .C c,     _   => c
  | .add a b, env => a.eval env + b.eval env
  | .mul a b, env => a.eval env * b.eval env
  | .neg a,   env => -(a.eval env)

/-- The monomial for variable `i` (reuses PolyNatM's). -/
def varMono : Nat → List Nat
  | 0     => [1]
  | i + 1 => 0 :: varMono i

theorem varMono_evalZ : ∀ i env, monoEvalZ (varMono i) env = env.getD i 0
  | 0,     env => by
      show powInt (env.headD 0) 1 * monoEvalZ [] env.tail = env.getD 0 0
      show (1 * env.headD 0) * 1 = env.getD 0 0
      rw [one_mulZ, mul_one]; cases env <;> rfl
  | i + 1, env => by
      show powInt (env.headD 0) 0 * monoEvalZ (varMono i) env.tail = env.getD (i+1) 0
      show (1 : Int) * monoEvalZ (varMono i) env.tail = env.getD (i+1) 0
      rw [one_mulZ, varMono_evalZ i env.tail]; cases env <;> rfl

def PE.norm : PE → List (List Nat × Int)
  | .var i   => [(varMono i, 1)]
  | .C c     => [([], c)]
  | .add a b => addNFZ a.norm b.norm
  | .mul a b => mulNFZ a.norm b.norm
  | .neg a   => negNFZ a.norm

theorem norm_evalZ : ∀ (e : PE) env, nfEvalZ e.norm env = e.eval env
  | .var i,   env => by
      show (1:Int) * monoEvalZ (varMono i) env + 0 = env.getD i 0
      rw [one_mulZ, Int.add_zero, varMono_evalZ i env]
  | .C c,     env => by show c * 1 + 0 = c; rw [mul_one, Int.add_zero]
  | .add a b, env => by
      show nfEvalZ (addNFZ a.norm b.norm) env = a.eval env + b.eval env
      rw [addNFZ_eval, norm_evalZ a env, norm_evalZ b env]
  | .mul a b, env => by
      show nfEvalZ (mulNFZ a.norm b.norm) env = a.eval env * b.eval env
      rw [mulNFZ_eval, norm_evalZ a env, norm_evalZ b env]
  | .neg a,   env => by
      show nfEvalZ (negNFZ a.norm) env = -(a.eval env)
      rw [negNFZ_eval, norm_evalZ a env]

/-- ★★★ **The reflection driver** for multivariate `Int` polynomial identities. -/
theorem poly_idMZ (eL eR : PE) (h : eL.norm = eR.norm) (env : List Int) :
    eL.eval env = eR.eval env := by
  rw [← norm_evalZ eL env, ← norm_evalZ eR env, h]

end E213.Meta.Int213.PolyIntM
