import E213.Meta.Tactic.NatHelper

/-!
# `PolyNat` — a ∅-axiom reflection prover for univariate `Nat` polynomial identities

Lean-core `ring`/`omega` are unavailable (Mathlib-free) or `propext`-dirty, so
nonlinear `Nat` identities like `(n+1)·(n+1) = n·n + 2·n + 1` had to be ground out by
hand with `add_mul`/`mul_assoc`/`mul_comm` chains.  This file replaces that with
**reflection**: a polynomial expression is reified into a syntax tree `PE`, normalised
to a Horner coefficient list, and two expressions with the *same* normal form
evaluate equally.  The coefficient lists are closed `List Nat`, so equality is `rfl`
— no `decide`, no `propext`, no `Classical`.

Usage (manual reification — mirror each side of the goal as a `PE` over the variable
`X`, then `rfl` on the normal forms):

```lean
example (n : Nat) : (n+1)*(n+1) = n*n + (2*n + 1) :=
  poly_id (.mul (.add .X (.C 1)) (.add .X (.C 1)))
          (.add (.mul .X .X) (.add (.mul (.C 2) .X) (.C 1)))
          rfl n
```

`poly_id eL eR rfl n` proves `eL.eval n = eR.eval n`; since `PE.eval` of a tree that
mirrors an expression reduces to that expression by `rfl`, the result is accepted as
the original (sub-free) `Nat` identity.  `PE` carries only `+`, `*`, constants and the
single variable `X` — `Nat` subtraction truncates and is not a polynomial operation,
so it is intentionally absent.

All zero-axiom.
-/

namespace E213.Meta.Nat.PolyNat

open E213.Tactic.NatHelper (add_mul mul_assoc mul_left_comm)

/-- A univariate `Nat` polynomial expression: the variable `X`, constants, sums and
    products.  (No subtraction — `Nat` `-` truncates and is not polynomial.) -/
inductive PE where
  | X : PE
  | C : Nat → PE
  | add : PE → PE → PE
  | mul : PE → PE → PE

/-- Evaluate a `PE` at a point `n`. -/
def PE.eval : PE → Nat → Nat
  | .X,       n => n
  | .C c,     _ => c
  | .add a b, n => a.eval n + b.eval n
  | .mul a b, n => a.eval n * b.eval n

/-- Horner evaluation of a coefficient list (low degree first):
    `[c₀, c₁, …] ↦ c₀ + n·(c₁ + n·(…))`. -/
def nfEval : List Nat → Nat → Nat
  | [],      _ => 0
  | c :: cs, n => c + n * nfEval cs n

/-- Coefficient-wise addition of two polynomials (padding the shorter).  Disjoint
    patterns on the first argument so closed forms reduce by `rfl`. -/
def nfAdd : List Nat → List Nat → List Nat
  | [],      q       => q
  | a :: p,  []      => a :: p
  | a :: p,  b :: q  => (a + b) :: nfAdd p q

/-- Scale a polynomial by a constant. -/
def nfScale : Nat → List Nat → List Nat
  | _, []      => []
  | a, b :: q  => a * b :: nfScale a q

/-- Polynomial multiplication (convolution via scale + shift). -/
def nfMul : List Nat → List Nat → List Nat
  | [],     _ => []
  | a :: p, q => nfAdd (nfScale a q) (0 :: nfMul p q)

/-- Normal form of a `PE`: its Horner coefficient list. -/
def PE.norm : PE → List Nat
  | .X       => [0, 1]
  | .C c     => [c]
  | .add a b => nfAdd a.norm b.norm
  | .mul a b => nfMul a.norm b.norm

/-! ## Soundness — `nfEval ∘ norm = eval` -/

theorem nfScale_eval (a : Nat) : ∀ q n, nfEval (nfScale a q) n = a * nfEval q n
  | [],     _ => by show (0:Nat) = a * 0; rw [Nat.mul_zero]
  | b :: q, n => by
    show a * b + n * nfEval (nfScale a q) n = a * (b + n * nfEval q n)
    rw [nfScale_eval a q n, Nat.mul_add a b (n * nfEval q n)]
    congr 1
    exact mul_left_comm n a (nfEval q n)

theorem nfAdd_eval : ∀ p q n, nfEval (nfAdd p q) n = nfEval p n + nfEval q n
  | [],     q,      n => by show nfEval q n = 0 + nfEval q n; rw [Nat.zero_add]
  | a :: p, [],     n => by show nfEval (a::p) n = nfEval (a::p) n + 0; rw [Nat.add_zero]
  | a :: p, b :: q, n => by
    show (a + b) + n * nfEval (nfAdd p q) n
       = (a + n * nfEval p n) + (b + n * nfEval q n)
    rw [nfAdd_eval p q n, Nat.mul_add n (nfEval p n) (nfEval q n),
        Nat.add_add_add_comm a (n * nfEval p n) b (n * nfEval q n)]

theorem nfMul_eval : ∀ p q n, nfEval (nfMul p q) n = nfEval p n * nfEval q n
  | [],     q, n => by show (0:Nat) = 0 * nfEval q n; rw [Nat.zero_mul]
  | a :: p, q, n => by
    show nfEval (nfAdd (nfScale a q) (0 :: nfMul p q)) n
       = (a + n * nfEval p n) * nfEval q n
    rw [nfAdd_eval, nfScale_eval]
    show a * nfEval q n + (0 + n * nfEval (nfMul p q) n)
       = (a + n * nfEval p n) * nfEval q n
    rw [Nat.zero_add, nfMul_eval p q n, add_mul a (n * nfEval p n) (nfEval q n),
        mul_assoc n (nfEval p n) (nfEval q n)]

/-- The reflection soundness theorem: a `PE` evaluates the same as its normal form. -/
theorem norm_eval : ∀ (e : PE) n, nfEval e.norm n = e.eval n
  | .X,       n => by
    show 0 + n * (1 + n * 0) = n
    rw [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.zero_add]
  | .C c,     n => by show c + n * 0 = c; rw [Nat.mul_zero, Nat.add_zero]
  | .add a b, n => by
    show nfEval (nfAdd a.norm b.norm) n = a.eval n + b.eval n
    rw [nfAdd_eval, norm_eval a n, norm_eval b n]
  | .mul a b, n => by
    show nfEval (nfMul a.norm b.norm) n = a.eval n * b.eval n
    rw [nfMul_eval, norm_eval a n, norm_eval b n]

/-- ★★★ **The reflection driver.**  Two polynomial expressions with equal normal
    forms evaluate equally everywhere.  Apply with `h := rfl` (the normal forms are
    closed `List Nat`): `poly_id eL eR rfl n : eL.eval n = eR.eval n`, where each
    `PE.eval` reduces by `rfl` to the mirrored `Nat` expression. -/
theorem poly_id (eL eR : PE) (h : eL.norm = eR.norm) (n : Nat) :
    eL.eval n = eR.eval n := by
  rw [← norm_eval eL n, ← norm_eval eR n, h]

end E213.Meta.Nat.PolyNat
