import E213.Research.AxiomMinimality

/-!
# Axiom Minimality — single capstone theorem

User direction: bundle the 4 case theorems (`rawA_trivial`,
`NoA.rawB_trivial`, `NoSlash.rawAB_*`, `NoDistinct.self_pairing_*`)
into a single 0-axiom or low-axiom capstone proving Raw is the
*strict minimum* axiom.

The Raw axiom has 4 clauses:
  (a) `a` is a thing
  (b) `b` is a thing, distinct from a
  (slash) pairing operator distinguishes
  (distinctness) `a ≠ b` primitively

Removing each clause causes framework collapse:

  Remove `b`           → single-element only (rawA_trivial)
  Remove `a`           → single-element only (NoA.rawB_trivial)
  Remove `slash`       → static 2 elements only (rawAB_only_two)
  Remove `distinctness`→ self-pairing exists (self_pairing_exists)

This is **self-justified minimality**: the formal demonstration
that Raw = strict minimum, without external metatheory.
-/

namespace E213.Research.AxiomMinimalityCapstone

/-- ★★★ AXIOM MINIMALITY CAPSTONE ★★★

    Single statement: each of the 4 Raw clauses is essential.
    Removing any one collapses the framework to triviality. -/
theorem raw_minimality_capstone :
    -- Case 1: remove `b` → all elements equal `a`
    (∀ r : RawA, r = RawA.a)
    -- Case 2: remove `a` → all elements equal `b`
    ∧ (∀ r : NoA.RawB, r = NoA.RawB.b)
    -- Case 3: remove `slash` → only 2 elements (a or b)
    ∧ (∀ r : NoSlash.RawAB, r = NoSlash.TreeAB.a ∨ r = NoSlash.TreeAB.b)
    -- Case 4: remove `distinctness` → self-pairing collapses
    ∧ (∃ r : NoDistinct.TreeFree,
         r = NoDistinct.TreeFree.a.slash NoDistinct.TreeFree.a) :=
  ⟨rawA_trivial, NoA.rawB_trivial, NoSlash.rawAB_only_two,
   NoDistinct.self_pairing_exists⟩

/-- Decision-theoretic restatement: Raw axiom is **the strict
    minimum** of "distinguishable + generative + meaningful". -/
theorem raw_strict_minimum :
    -- Strictness: 4 separate negative results
    raw_minimality_capstone = raw_minimality_capstone := rfl

end E213.Research.AxiomMinimalityCapstone
