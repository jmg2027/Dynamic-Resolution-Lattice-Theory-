# Frontier: rearrangement inequality, general-n reverse/permutation form

`Analysis/RearrangementInequality` (20 PURE) closed the exchange CORE
(`swap_slack`, `swap_inequality`: similarly-sorted dominates the swapped pairing,
slack = `(aⱼ−aᵢ)(bⱼ−bᵢ) ≥ 0`) + the n=2,3 reverse-vs-sorted cases over arbitrary
`a b : Nat → Int`.

**Open:** the general-n statement `reverse_le_sorted (mono a)(mono b) :
sumI (a·b∘rev) n ≤ sumI (a·b) n`, and the full permutation form (identity pairing
maximizes Σ aᵢ b_{σ(i)} over all σ). Needs the **bubble-sort exchange induction**:
any permutation is reachable from sorted by adjacent transpositions, each fixing an
inversion non-decreasingly (`swap_inequality` is the step). Chebyshev's
`chebyshev_sum` is NOT a drop-in (different quantity). The blocker is a clean ∅-axiom
permutation/transposition representation + the induction; do interactively or with a
`Fin`-permutation-as-list-of-swaps encoding.
