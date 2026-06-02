import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PureNat

/-!
# `PolyNatM` — a ∅-axiom reflection prover for *multivariate* `Nat` polynomial identities

`Meta/Nat/PolyNat` is univariate, `Meta/Int213/PolyInt2` bivariate.  Identities with three or
more `Nat` variables (e.g. the `cube_reorder` / `cubic_eq` reorders in `DepthCubicGeneric`,
the `casoratian` cross-identities) fall outside both, and Lean-core `ring`/`omega`/`ac_rfl`
are unavailable or `propext`-dirty.  This file fills the gap by **reflection** with a flat
monomial-map normal form.

A monomial is an exponent vector `List Nat` (position `i` = exponent of variable `i`); a
polynomial normal form is a `List (List Nat × Nat)` (monomial → coefficient), kept sorted by
the monomial order `monoLt` and merged, so two expressions denoting the same polynomial have
the **same** normal form — a closed `List (List Nat × Nat)`, equal by `rfl`.  Base monomials
are canonical (`var i` ends in `1`, constants are `[]`), and `monoMul = zipAdd` preserves
"ends nonzero", so no trailing zeros ever arise.

Usage (manual reification — mirror each side as a `PE` over `var 0, var 1, …`):

```lean
example (x y z : Nat) : (x + y) * z = z * x + y * z :=
  poly_idM
    (.mul (.add (.var 0) (.var 1)) (.var 2))
    (.add (.mul (.var 2) (.var 0)) (.mul (.var 1) (.var 2)))
    rfl [x, y, z]
```

All zero-axiom.
-/

namespace E213.Meta.Nat.PolyNatM

open E213.Tactic.NatHelper (mul_mul_mul_comm_213 add_mul)
open E213.Meta.Nat.PureNat (pow_add)

/-! ## §1 — monomials (exponent vectors) -/

/-- Evaluate a monomial (exponent vector) at an environment `env` (variable values,
    positionally; missing variables read as `0`). -/
def monoEval : List Nat → List Nat → Nat
  | [],      _   => 1
  | e :: es, env => (env.headD 0) ^ e * monoEval es env.tail

/-- Pointwise exponent addition (monomial product), padding the shorter. -/
def zipAdd : List Nat → List Nat → List Nat
  | [],      q       => q
  | a :: as, []      => a :: as
  | a :: as, b :: bs => (a + b) :: zipAdd as bs

/-- ★ Monomial product evaluates to the product of evaluations (`pow_add` per variable). -/
theorem zipAdd_eval : ∀ a b env, monoEval (zipAdd a b) env = monoEval a env * monoEval b env
  | [],      b,      env => by show monoEval b env = 1 * monoEval b env; rw [Nat.one_mul]
  | a :: as, [],     env => by show monoEval (a::as) env = monoEval (a::as) env * 1; rw [Nat.mul_one]
  | a :: as, b :: bs, env => by
      show (env.headD 0) ^ (a + b) * monoEval (zipAdd as bs) env.tail
         = ((env.headD 0) ^ a * monoEval as env.tail) * ((env.headD 0) ^ b * monoEval bs env.tail)
      rw [pow_add, zipAdd_eval as bs env.tail]
      exact mul_mul_mul_comm_213 _ _ _ _

/-- Structural Boolean equality of monomials (`Nat.beq`, which reduces structurally so the
    proofs stay ∅-axiom — `==`/`eq_of_beq` route pulls `propext`/`Quot.sound`). -/
def monoBeq : List Nat → List Nat → Bool
  | [],      []      => true
  | [],      _ :: _  => false
  | _ :: _,  []      => false
  | a :: as, b :: bs => Nat.beq a b && monoBeq as bs

/-- PURE `Nat` equality from `Nat.beq`. -/
theorem nat_eq_of_beq : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0,     0,     _ => rfl
  | 0,     _ + 1, h => Bool.noConfusion h
  | _ + 1, 0,     h => Bool.noConfusion h
  | a + 1, b + 1, h => by
      have h' : Nat.beq a b = true := h
      rw [nat_eq_of_beq h']

theorem eq_of_monoBeq : ∀ {m m' : List Nat}, monoBeq m m' = true → m = m'
  | [],      [],      _ => rfl
  | [],      _ :: _,  h => Bool.noConfusion h
  | _ :: _,  [],      h => Bool.noConfusion h
  | a :: as, b :: bs, h => by
      have h2 : (Nat.beq a b && monoBeq as bs) = true := h
      cases hab : Nat.beq a b with
      | false => rw [hab] at h2; exact Bool.noConfusion h2
      | true  => rw [hab] at h2; rw [nat_eq_of_beq hab, eq_of_monoBeq h2]

/-- Lexicographic Boolean order on monomials (only used to canonicalise; soundness does not
    depend on it being a correct order). -/
def monoLt : List Nat → List Nat → Bool
  | [],      []      => false
  | [],      _ :: _  => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else monoLt as bs

/-! ## §2 — normal form (sorted monomial → coefficient list) -/

/-- Evaluate a normal form. -/
def nfEval : List (List Nat × Nat) → List Nat → Nat
  | [],            _   => 0
  | (m, c) :: rest, env => c * monoEval m env + nfEval rest env

/-- Insert `(m, c)` into a sorted normal form, merging equal monomials. -/
def insertAdd (m : List Nat) (c : Nat) : List (List Nat × Nat) → List (List Nat × Nat)
  | []             => [(m, c)]
  | (m', c') :: rest =>
      if monoBeq m m' then (m', c + c') :: rest
      else if monoLt m m' then (m, c) :: (m', c') :: rest
      else (m', c') :: insertAdd m c rest

theorem insertAdd_eval (m : List Nat) (c : Nat) :
    ∀ nf env, nfEval (insertAdd m c nf) env = c * monoEval m env + nfEval nf env
  | [],              _   => rfl
  | (m', c') :: rest, env => by
      show nfEval (if monoBeq m m' then ((m', c + c') :: rest)
                   else if monoLt m m' then ((m, c) :: (m', c') :: rest)
                   else ((m', c') :: insertAdd m c rest)) env
         = c * monoEval m env + (c' * monoEval m' env + nfEval rest env)
      cases hb : monoBeq m m' with
      | true =>
          have hmm : m = m' := eq_of_monoBeq hb
          show (c + c') * monoEval m' env + nfEval rest env
             = c * monoEval m env + (c' * monoEval m' env + nfEval rest env)
          rw [hmm, add_mul c c' (monoEval m' env), Nat.add_assoc]
      | false =>
          cases hl : monoLt m m' with
          | true => rfl
          | false =>
              show c' * monoEval m' env + nfEval (insertAdd m c rest) env
                 = c * monoEval m env + (c' * monoEval m' env + nfEval rest env)
              rw [insertAdd_eval m c rest env, ← Nat.add_assoc, ← Nat.add_assoc,
                  Nat.add_comm (c' * monoEval m' env) (c * monoEval m env)]

/-- Sum of two normal forms (insert each term of `p`). -/
def addNF : List (List Nat × Nat) → List (List Nat × Nat) → List (List Nat × Nat)
  | [],             q => q
  | (m, c) :: rest, q => insertAdd m c (addNF rest q)

theorem addNF_eval : ∀ p q env, nfEval (addNF p q) env = nfEval p env + nfEval q env
  | [],             q, env => by show nfEval q env = 0 + nfEval q env; rw [Nat.zero_add]
  | (m, c) :: rest, q, env => by
      show nfEval (insertAdd m c (addNF rest q)) env
         = c * monoEval m env + nfEval rest env + nfEval q env
      rw [insertAdd_eval m c (addNF rest q) env, addNF_eval rest q env, Nat.add_assoc]

/-- Multiply a normal form by a single monomial-coefficient. -/
def scaleNF (m0 : List Nat) (c0 : Nat) : List (List Nat × Nat) → List (List Nat × Nat)
  | []             => []
  | (m, c) :: rest => insertAdd (zipAdd m0 m) (c0 * c) (scaleNF m0 c0 rest)

theorem scaleNF_eval (m0 : List Nat) (c0 : Nat) :
    ∀ q env, nfEval (scaleNF m0 c0 q) env = (c0 * monoEval m0 env) * nfEval q env
  | [],             env => by show (0:Nat) = (c0 * monoEval m0 env) * 0; rw [Nat.mul_zero]
  | (m, c) :: rest, env => by
      show nfEval (insertAdd (zipAdd m0 m) (c0 * c) (scaleNF m0 c0 rest)) env
         = (c0 * monoEval m0 env) * (c * monoEval m env + nfEval rest env)
      rw [insertAdd_eval (zipAdd m0 m) (c0 * c) (scaleNF m0 c0 rest) env,
          scaleNF_eval m0 c0 rest env, zipAdd_eval m0 m env,
          Nat.mul_add (c0 * monoEval m0 env) (c * monoEval m env) (nfEval rest env)]
      congr 1
      exact mul_mul_mul_comm_213 c0 c (monoEval m0 env) (monoEval m env)

/-- Product of two normal forms. -/
def mulNF : List (List Nat × Nat) → List (List Nat × Nat) → List (List Nat × Nat)
  | [],             _ => []
  | (m, c) :: rest, q => addNF (scaleNF m c q) (mulNF rest q)

theorem mulNF_eval : ∀ p q env, nfEval (mulNF p q) env = nfEval p env * nfEval q env
  | [],             q, env => by show (0:Nat) = 0 * nfEval q env; rw [Nat.zero_mul]
  | (m, c) :: rest, q, env => by
      show nfEval (addNF (scaleNF m c q) (mulNF rest q)) env
         = (c * monoEval m env + nfEval rest env) * nfEval q env
      rw [addNF_eval (scaleNF m c q) (mulNF rest q) env, scaleNF_eval m c q env,
          mulNF_eval rest q env, add_mul (c * monoEval m env) (nfEval rest env) (nfEval q env)]

/-! ## §3 — the expression type, normal form, and the driver -/

/-- A multivariate `Nat` polynomial expression: indexed variables, constants, sums,
    products. -/
inductive PE where
  | var : Nat → PE
  | C   : Nat → PE
  | add : PE → PE → PE
  | mul : PE → PE → PE

/-- Evaluate a `PE` at an environment. -/
def PE.eval : PE → List Nat → Nat
  | .var i,   env => env.getD i 0
  | .C c,     _   => c
  | .add a b, env => a.eval env + b.eval env
  | .mul a b, env => a.eval env * b.eval env

/-- The monomial for variable `i`: `i` zeros then a `1`. -/
def varMono : Nat → List Nat
  | 0     => [1]
  | i + 1 => 0 :: varMono i

theorem varMono_eval : ∀ i env, monoEval (varMono i) env = env.getD i 0
  | 0,     env => by
      show (env.headD 0) ^ 1 * monoEval [] env.tail = env.getD 0 0
      rw [Nat.pow_one]
      show env.headD 0 * 1 = env.getD 0 0
      rw [Nat.mul_one]
      cases env <;> rfl
  | i + 1, env => by
      show (env.headD 0) ^ 0 * monoEval (varMono i) env.tail = env.getD (i+1) 0
      rw [Nat.pow_zero, Nat.one_mul, varMono_eval i env.tail]
      cases env <;> rfl

/-- Normal form of a `PE`. -/
def PE.norm : PE → List (List Nat × Nat)
  | .var i   => [(varMono i, 1)]
  | .C c     => [([], c)]
  | .add a b => addNF a.norm b.norm
  | .mul a b => mulNF a.norm b.norm

theorem norm_eval : ∀ (e : PE) env, nfEval e.norm env = e.eval env
  | .var i,   env => by
      show 1 * monoEval (varMono i) env + 0 = env.getD i 0
      rw [Nat.one_mul, Nat.add_zero, varMono_eval i env]
  | .C c,     env => by show c * 1 + 0 = c; rw [Nat.mul_one, Nat.add_zero]
  | .add a b, env => by
      show nfEval (addNF a.norm b.norm) env = a.eval env + b.eval env
      rw [addNF_eval, norm_eval a env, norm_eval b env]
  | .mul a b, env => by
      show nfEval (mulNF a.norm b.norm) env = a.eval env * b.eval env
      rw [mulNF_eval, norm_eval a env, norm_eval b env]

/-- ★★★ **The reflection driver.**  Two multivariate `Nat` polynomial expressions with equal
    normal forms evaluate equally at every environment.  Apply with `h := rfl` (the normal
    forms are closed `List (List Nat × Nat)`): `poly_idM eL eR rfl env`. -/
theorem poly_idM (eL eR : PE) (h : eL.norm = eR.norm) (env : List Nat) :
    eL.eval env = eR.eval env := by
  rw [← norm_eval eL env, ← norm_eval eR env, h]

end E213.Meta.Nat.PolyNatM
