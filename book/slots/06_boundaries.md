# 6 · Boundaries, and the open programme

## Fold-back: why axes stop, and where tuples end

Adjoining an answer `α` a priori opens infinitely many axes — `α`,
`α²`, `α³`, … .  An equation is a **fold-back rule**: `a·αⁿ =
(lower terms)` returns the n-th power to the span of the first `n`,
so the axes stop at the degree.  Degree 1 folds `α` itself into the
base — that is what "collapse" ever was.  No fold-back at all — the
unknown sitting in an exponent slot, as a class — and no finite tuple
suffices: the question leaves equation territory for **sandwich-family
data** (cuts), the subject of the `Real213` volume.  The boundary is
grammar-relative: each admissible question grammar pins its own
countable family, and what is "transcendental" is so *relative to a
grammar*, not absolutely.

## The interaction wall

Lifting an operation onto its *own* pairs is slotwise and costs only
the medial law (chapter 3).  Lifting a **different** operation onto a
pair layer is governed by the interaction law, and the wall this
volume once stated as a slogan is now two separate theorems
(`PairOp.cross_rule_forced`, `pow_lift_impossible`):

* **With the distributive selector** (bi-distributivity over the
  pair addition), the lift of × is *forced* — one unit value and
  three annihilation instances, each a single cross-equation,
  determine the cross rule `(ac+bd, ad+bc)` on every pair, with full
  congruence and extension as corollaries.  And under the same
  selector an operation that does not already bi-distribute on the
  base has **no lift at all**: bi-additivity over the readout admits
  only multiples of ×, and `2³ = 8 ≠ 2·3` kills `^` (a fortiori
  tetration) — nonexistence, not non-canonicity.
* **Without the selector**, congruent extensions are plentiful
  (flatten and apply) and nothing internal selects one — *that* is
  the genuinely canonical-less regime.

The deeper rung-3 wall is that `^`'s own exponent law admits no
congruent pair extension (a negative exponent would need
`2¹·2^{(0,1)} ≈ 1` among the readouts), and `↑↑`'s defining recursion
cannot even be stated on pairs — `(2↑↑2)↑↑2 = 256` while
`2↑↑4 = 65536`, and `2⁴ = 4²` shows depth-2 fibers are wild.  So the
recursion "each root-completion is the previous completion re-run
inside the exponent lattice" runs for exactly three rungs and
terminates — and the wall is a proved absence, which is more
informative than the false unbounded ladder.

## Wrapping, again

The mod world threads the whole volume and lands in one sentence:
**progressive operations are primary; wrapping operations are their
fiber readouts.**  The witness sets of a wrap question are arithmetic
progressions — sorted lists again, with a larger unit — so the wrap
layer's numbers are periodic classes, its canonical remainder is a
flattening Lens (`2 mod 2` is the class of `2`, not `0`), and its
"loss" of cancellation is precisely the information that a class, not
a point, has been minted.

## The open programme

Each frontier below continues a closed theorem; none floats free.

1. **The interaction-law rung**: derive the cross rule on +-pairs
   *from* distributivity as the unique relation-respecting lift —
   completing the meta-operation: one operation in, the whole pair
   layer and its compatible arithmetic out.
2. **The wrap relation in witness form**
   (`∃ i j, a + i·n = b + j·n`), with the canonical remainder proved
   to be its faithful flattening — ℤ/n without normalization.
3. **`pairEq` for `^`**: the generic transitivity proof fails (no
   commutativity), yet over ℕ the relation may be transitive anyway,
   by unique factorization — the first place where *holds* and *holds
   for the generic reason* split.
4. **The minimal polynomial as the next rung's lowest terms**:
   existence and uniqueness mirroring `gcd_strip_coprime` and
   `coprime_repr_unique` one level up, with Gauss's lemma as the
   gcd-strip of coefficient tuples.
5. **The exponent lattice made explicit**: multiplicativity and
   separation for the per-prime exponent readout — the ground on
   which `√2`'s witness criterion ("all exponents divisible") becomes
   a theorem.
6. **Per-frame visibility as a theorem schema**: `(∃x, p ∣ x²+1) ↔
   p % 4 = 1` and beyond — the dichotomy of chapter 5's last section,
   frame by frame.

The method does not change as the programme advances: a sorted list,
total operations, questions, witnesses, sandwiches — and the empty
axiom set as the standing proof that nothing else was ever used.
