/-!
# Logic — Cut as predicate calculus

In 213, a *predicate* on `(Nat, Nat)` is just `Cut := Nat → Nat → Bool`.
Logical connectives are `Bool` operations: `&&`, `||`, `xor`, `not`.

This is **predicate calculus done by Lean's native decidable Bool
arithmetic** — no propext, no LEM, no Classical.  All identities
below are atomic `decide`/`rfl` Bool truth tables.
-/

namespace E213.Lib.Math.Combinatorics.Logic.Predicate

/-- A `Cut`-style predicate over `(m, k)`. -/
abbrev Predicate := Nat → Nat → Bool

/-- Always-true predicate. -/
def truePred : Predicate := fun _ _ => true

/-- Always-false predicate. -/
def falsePred : Predicate := fun _ _ => false

/-- Conjunction of predicates. -/
def andP (p q : Predicate) : Predicate := fun m k => p m k && q m k

/-- Disjunction of predicates. -/
def orP (p q : Predicate) : Predicate := fun m k => p m k || q m k

/-- Negation of a predicate. -/
def notP (p : Predicate) : Predicate := fun m k => !(p m k)

/-- Implication: `p → q ≡ ¬p ∨ q`. -/
def impP (p q : Predicate) : Predicate := orP (notP p) q

/-- Predicate equality (pointwise). -/
def predEq (p q : Predicate) : Prop := ∀ m k, p m k = q m k

/-- ★ **Double negation = identity** ★ — atomic Bool truth.
    Externally consumed by `Logic/Capstone`. -/
theorem double_neg (p : Predicate) : predEq (notP (notP p)) p :=
  fun m k => Bool.not_not (p m k)

/-- ★ **De Morgan #1**: `¬(p ∧ q) = ¬p ∨ ¬q` (atomic).
    Externally consumed by `Logic/Capstone`. -/
theorem deMorgan_and (p q : Predicate) :
    predEq (notP (andP p q)) (orP (notP p) (notP q)) :=
  fun m k => Bool.not_and (p m k) (q m k)

/-- True is identity for `andP`.  Externally consumed by `Logic/Capstone`. -/
theorem and_true_id (p : Predicate) : predEq (andP p truePred) p :=
  fun m k => Bool.and_true (p m k)

/-- ★ Predicate-calculus supplementary master — reflexivity of
    predEq, De Morgan #2, commutativity (and/or), or-false identity. -/
theorem predicate_master (p q : Predicate) :
    predEq p p
    ∧ predEq (notP (orP p q)) (andP (notP p) (notP q))
    ∧ predEq (andP p q) (andP q p)
    ∧ predEq (orP p q) (orP q p)
    ∧ predEq (orP p falsePred) p :=
  ⟨fun _ _ => rfl,
   fun m k => Bool.not_or (p m k) (q m k),
   fun m k => Bool.and_comm (p m k) (q m k),
   fun m k => Bool.or_comm (p m k) (q m k),
   fun m k => Bool.or_false (p m k)⟩

end E213.Lib.Math.Combinatorics.Logic.Predicate
