/-!
# E213.Term.Term — deep-embedded AST of 213.

Vision: Lean is the syntactic host, 213 is the real kernel.
Term is *data*, and all meaning is determined by *total functions* over Term.
None of Lean's propext / Quot.sound / Classical is load-bearing
for the meaning of Term.

Raw primitives (CLAUDE.md axiom: "things exist with pairwise relations"):
  zero  : absence of distinguishing structure in Raw
  succ  : adding a new entity to Raw
  add   : counting composition
  mul   : pairwise grouping (Cartesian)

The next layer defines entity arithmetic + Lens distinction via add/mul.
-/

namespace E213.Term

inductive Term : Type
  | zero : Term
  | succ : Term → Term
  | add  : Term → Term → Term
  | mul  : Term → Term → Term
  deriving Repr

namespace Term

/-- 213 standard constants (CLAUDE.md "Key Constants"). -/
protected def nS : Term := succ (succ (succ zero))      -- 3
protected def nT : Term := succ (succ zero)              -- 2
protected def d  : Term :=                                -- 5
  succ (succ (succ (succ (succ zero))))
protected def c  : Term := succ (succ zero)              -- 2

/-- Raw eval of Term: Term → ℕ.
    Uses structural recursion + core arithmetic only → 0 axiom. -/
protected def eval : Term → Nat
  | zero      => 0
  | succ t    => Nat.succ (Term.eval t)
  | add a b   => Term.eval a + Term.eval b
  | mul a b   => Term.eval a * Term.eval b

/-- 213-internal equivalence: two Terms eval to the same ℕ.
    Returns Bool — bypasses Prop equality / propext. -/
protected def equiv (a b : Term) : Bool := Nat.beq (Term.eval a) (Term.eval b)

end Term
end E213.Term
