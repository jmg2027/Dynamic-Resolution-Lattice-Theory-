import E213.Lib.Math.Infinity.Cantor
import E213.Lib.Math.Infinity.Countable
import E213.Prelude

/-!
# Infinity.Chain: chain-space cardinality and R5b reinterpretation

A **chain** in Raw is a function `Nat → Raw`.  The set of
all chains has cardinality strictly greater than Raw (= ℕ):
no surjection `Nat → (Nat → Raw)` exists.

This gives a Raw-internal reading of the paper's R5b
condition:
- R5b (paper): "every non-terminating structural branch
  has a uniquely determined state in α".
- Raw-internal reading: the chain-space `Nat → Raw` is
  uncountable; a Lens codomain receiving all chains with
  uniquely determined limit-states needs uncountable
  cardinality.
- The classical-infinity step (from uncountable + order
  structure to Cauchy completeness forcing ℝ) still sits
  outside Raw+Lens, but the **cardinality demand is
  Raw-internal**, proved here.

Proof: Cantor's diagonal.  Given `f : ℕ → (ℕ → Raw)`, define
`g n := if f n n = Raw.a then Raw.b else Raw.a`.  Then
`g n ≠ f n n` for all `n`, so `g` is not in the image of
`f`.
-/

namespace E213.Infinity

open E213.Theory

/-- **Chain-space uncountability.**  No function `ℕ → (ℕ →
    Raw)` is surjective. -/
theorem chain_uncountable :
    ¬ ∃ f : Nat → (Nat → Raw), Function.Surjective f := by
  rintro ⟨f, hf⟩
  let g : Nat → Raw :=
    fun n => if f n n = Raw.a then Raw.b else Raw.a
  obtain ⟨k, hk⟩ := hf g
  have hpoint : f k k = g k := congrFun hk k
  by_cases hval : f k k = Raw.a
  · have hg : g k = Raw.b := by
      show (if f k k = Raw.a then Raw.b else Raw.a) = Raw.b
      rw [if_pos hval]
    rw [hg, hval] at hpoint
    exact absurd hpoint (by decide)
  · have hg : g k = Raw.a := by
      show (if f k k = Raw.a then Raw.b else Raw.a) = Raw.a
      rw [if_neg hval]
    rw [hg] at hpoint
    exact absurd hpoint hval

end E213.Infinity
