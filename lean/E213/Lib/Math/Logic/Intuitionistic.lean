import E213.Lib.Math.Logic.Predicate

/-!
# Logic — Intuitionistic / constructive

213 is constructive: every theorem must show a *witness*.  Without
Choice, LEM (`p ∨ ¬p` for arbitrary `p`) is **not** automatic.

But on Bool — the native decidable truth type — LEM **does** hold
*atomically*: `b ∨ ¬b = true` for every `Bool`.  So at the Bool
level the constructive and classical readings coincide.

This file:

  * `bool_lem`: LEM for Bool (atomic, not classical).
  * `witness_of_exists_bool`: Bool-existential gives a witness directly.
  * `decidable_predicate`: Cut-style predicates are decidable at every
    `(m, k)` — no Classical.dec needed.

At the Prop level (where decidability is not assumed), LEM is
*not* asserted.  This is the "constructive only as feature"
character of the framework.
-/

namespace E213.Lib.Math.Logic.Intuitionistic

open E213.Lib.Math.Logic.Predicate

/-- ★ **Bool LEM is atomic** ★ — every Bool is either true or
    false; this is a direct decidable Bool computation, distinct
    from the propext-based Prop-level LEM. -/
theorem bool_lem (b : Bool) : b = true ∨ b = false := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- ★ **Predicate LEM at every point** ★ — `p m k = true ∨ p m k = false`.
    At the Bool level the constructive and classical readings
    coincide: each query has a decided Bool answer. -/
theorem predicate_lem (p : Predicate) (m k : Nat) :
    p m k = true ∨ p m k = false := bool_lem (p m k)

/-- LEM does NOT propagate to *uniform* satisfaction across all
    `(m, k)`: the predicate as a whole need not be uniformly true
    or uniformly false.  This is captured by `andP p (notP p)` not
    being uniformly false in propEq sense — but pointwise, it is. -/
theorem and_neg_self_pointwise (p : Predicate) (m k : Nat) :
    andP p (notP p) m k = false :=
  Bool.and_not_self (p m k)

/-- ★ **Constructive existential** ★ — for a Bool predicate, an
    existential witness is *literally* a (m, k) pair making it
    true.  No Classical.choice. -/
def boolExistsWitness (p : Predicate) (m k : Nat) (h : p m k = true) :
    Σ' m' k', p m' k' = true := ⟨m, k, h⟩

/-- The witness extraction is rfl-stable: caller's evidence
    becomes the existential's witness. -/
theorem witness_eq_input (p : Predicate) (m k : Nat) (h : p m k = true) :
    (boolExistsWitness p m k h).1 = m := rfl

/-- ★ **Witness-via-Bool**: any non-trivial Bool predicate has a
    decidable witness or counter-witness, with no Choice axiom.
    The "intuitionistic" content of 213 is precisely this
    Bool-decidability of the substrate. -/
theorem witness_or_counter (p : Predicate) (m k : Nat) :
    p m k = true ∨ ¬(p m k = true) := by
  cases h : p m k
  · exact Or.inr (fun hc => Bool.false_ne_true (h ▸ hc))
  · exact Or.inl rfl

end E213.Lib.Math.Logic.Intuitionistic
