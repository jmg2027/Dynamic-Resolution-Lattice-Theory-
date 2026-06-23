# The generation of ℕ's arithmetic — count-shadows of the distinguishing

**Status**: Closed for the additive/equational/order layer; the multiplicative-atom
(prime/FTA) layer is an open frontier (named below). Mirrors
`lean/E213/Meta/Nat/{UnitList, UnitGrid, UnitBox, UnitDistrib, UnitOrder,
ProdCount}.lean`.

## What this chapter establishes

The arithmetic of ℕ is not assumed — it is **generated**, law by law, as the
*count-shadow* of operations on lists of **units** (elements with no distinguishing
marks). Each algebraic law of ℕ is derived from a structural fact about unit lists
proved by induction alone, and — the discipline that makes this more than a restatement
— **no derivation presupposes the ℕ-law it produces**: the cone of each generated law
is verified free of that law (`add_assoc`-free, `mul_assoc`-free, `mul_add`-free,
`add_le_add`-free). The result is the complete *ordered commutative semiring*
`(ℕ, +, ·, 0, 1, ≤)`, generated; and a precise account of where generation stops — at
the multiplicative-atom (prime) structure — and why.

## The additive monoid — `+` is born from append

The carrier is `List Unit`: lists of indistinguishable units. The readout is
`count : List Unit → Nat` (how many units), and append is the primitive combine.

- **Append is associative** for any element type, free, by bare induction
  (`UnitList.append_assoc`); on *unit* lists it is also **commutative**
  (`UnitList.append_comm`) — indistinguishable elements carry no position information,
  so "arrangement" is no information to forget. (Distinguishable elements *do* remember
  it: `append_not_comm_general`, `[a]++[b] ≠ [b]++[a]`.)
- `count` is a homomorphism `append ↦ +` (`count_append_fwd`,
  `count (l ++ m) = count l + count m`).
- Hence `+`-**commutativity** is the count-shadow of `append_comm`
  (`add_comm_from_append`) and `+`-**associativity** the shadow of `append_assoc`
  (`add_assoc_from_append`, cone verified `Nat.add_assoc`-free). The additive monoid
  `(ℕ, +, 0)` is generated.

## The multiplicative monoid — `×` is born from the grid

The carrier rises one dimension: a 2-D **unit grid** (`UnitGrid`). An `a × b` grid of
units has a total cell count `total`; `total (rows a b) = a·b` (`total_rows`).

- `×`-**commutativity** is the **grid transpose** double-count: counting `rows a b`
  by rows gives `a·b`; counting its transpose (`b` columns of height `a`) gives `b·a`;
  the transpose is the same units, so the counts agree (`mul_comm_from_grid`) — no
  `Nat.mul_comm`.
- `×`-**associativity** is the 3-D **unit box** double-count: an `a×b×c` box counted as
  one `(a·b)×c` grid gives `(a·b)·c`; counted as `a` boxes of `b·c` cells gives
  `a·(b·c)` (`UnitBox.mul_assoc_from_box`, cone verified `Nat.mul_assoc`-free). The
  multiplicative monoid `(ℕ, ·, 1)` is generated.

## The operation tower — and where commutativity dies

`+` and `×` are the first two rungs of one ladder. The whole tower is a single
recursion `HyperLadder.hyperop`: rung 0 = successor, rung 1 = `+`, rung 2 = `·`, rung 3
= `^` (`hyperop_two`, `hyperop_three`), each rung the **count `b` iterating the rung
below**. Geometrically the ladder climbs dimension: `+` counts a 1-D list, `×` a 2-D
grid, `^` a `b`-dimensional unit **hypercube** — `count (hcube a b) = a^b`
(`UnitHyper.count_hcube`), `count = side ^ dim` (`count_eq_side_pow_dim`).

Commutativity holds for the first two rungs and **dies at the third**, for a precise
structural reason — not "a law is lost" but a **type-asymmetry exposed**. `+` commutes
because a 1-D list's count is its length (order-free); `×` commutes because the 2-D
grid's transpose is the same cells (`mul_comm_from_grid`). But `^` has two arguments of
*different kinds* — a **side** and a **dimension** — and swapping them changes the
object: `swap_changes_dim : dim (hcube 2 3) ≠ dim (hcube 3 2)` (`UnitHyper`). The
hypercube `2×2×2` (side 2, dim 3) and `3×3` (side 3, dim 2) are not the same shape, so
`2^3 ≠ 3^2` is the count-shadow of a genuine geometric difference, and `^`'s
non-commutativity (`HyperAssoc.pow_not_comm`) is *that* asymmetry read by the count —
commutativity is born where the counted object is symmetric and absent where it is not
(`theory/essays/analysis/where_commutativity_is_born.md`).

## The bridge — distributivity from the width-split

Left-distributivity `a·(b+c) = a·b + a·c` is the **grid width-split**: an `a × (b+c)`
grid separates into the `a×b` and `a×c` grids, and the column totals regroup additively
(`UnitDistrib.mul_add_from_grid`, cone `Nat.mul_add`-free; right-distributivity
`add_mul_from_grid` follows from the generated left form + generated `×`-comm). With
both distributive laws, the commutative semiring is complete as a generated discipline.

## The order — `≤` is born from extension

`≤` is the **prefix/extension** relation on unit lists: `a ≤ b ↔ ∃ l, fromNat a ++ l =
fromNat b` (`UnitOrder.le_iff_unit_extension`); `Nat.le` is the count-readout of "the
unit list of `b` extends that of `a`." Its compatibility with `+`
(`add_le_add_right`, `Nat.add_le_add_right`-free) is generated from the *same*
`append_comm` indistinguishability that births `+`-commutativity — the suffix and the
added block commute. So the **ordered commutative semiring `(ℕ, +, ·, 0, 1, ≤)` is
generated**.

## The +/× duality — distinguishability is the only difference

The multiplicative count-Lens `prodL : List Nat → Nat` (`ProdCount`) is the exact dual
of the additive `count`: a homomorphism `append ↦ ·` (`prodL_append`), reorder-invariant
from the generated `×`-comm (`prodL_swap`), so it factors through the **multiset**, not
the list. Reading one prime: `prodL (replicate k p) = p^k` (`prodL_replicate`) — the
exponent.

The duality is then a theorem. One construction — two blocks `replicate j _ ++
replicate k _` — read two ways:

- **additive** (`count`): the blocks **merge** into one number `j + k`, because the
  units are indistinguishable;
- **multiplicative** (`prodL`) with *distinct* atoms `p ≠ q`: the blocks stay
  **separate** as the exponent vector `p^j · q^k` (`prodL_two_atoms`), the pair `(j,k)`
  recoverable;
- **multiplicative with indistinguishable atoms** (`q = p`): the blocks **merge too** —
  `p^(j+k)` (`prodL_one_atom_merges`), exactly the additive `j+k`, one fold up.

So `×` *is* `+` whenever its atoms are made indistinguishable. **The entire excess of `×`
over `+` — the exponent vector, hence unique factorization — is precisely the
*distinguishability* of primes.** The dimension jump from one count (the length) to a
*vector* of counts (one per distinct prime) is the distinguishability, and nothing else.
This is the 213-native content of "addition and multiplication are two faces of one
count" (`theory/essays/synthesis/multiplicativity_is_the_x_count_lens.md`,
`theory/essays/synthesis/addition_and_multiplication_are_two_faces_of_one_count.md`).

## Where generation stops — and why (the honest terminus)

The additive decomposition `fromNat (n+1) = () :: fromNat n` is **structural**: the peel
takes `n+1 → n`, a predecessor step, on the inductive recursor (the count carrier's own
well-foundedness — the same shape as the Raw slash-peel `MuNuMirror.isPart_wf`). Every
law above is generated because its recursion is this structural peel.

Unique factorization (FTA) is different. Its decomposition peels `n → n / minFac n` — a
**non-structural**, well-founded-but-not-predecessor descent (it can divide by a large
prime, jumping far below `n−1`). So FTA completes on `Nat.strongRecOn`, a *borrowed*
well-foundedness, and **cannot** be a structural / additive-peel generation. It is a
genuinely *second* structure: the `exp`/`vp` Lens over **distinguishable** primes, dual
to the additive Lens but not reducible to it. Its uniqueness exists ∅-axiom
(`Lib/Math/NumberTheory/FTAUniqueness.factorization_unique` — the multiset is the
`vp`-vector), but on the non-structural descent.

This is the precise boundary of "generated vs borrowed": the additive/equational/order
structure of ℕ is generated from the distinguishing's own structural descent; the
multiplicative-atom structure is the open frontier where a Raw-native *multiplicative*
descent (a prime-distinguishability structure) would be needed for genuine generation.

## Lean source

`lean/E213/Meta/Nat/`: `UnitList` (additive monoid, 12 PURE), `UnitGrid` (×-comm, 15
PURE), `UnitBox` (×-assoc, 5 PURE), `UnitDistrib` (distributivity, 4 PURE), `UnitOrder`
(order, 3 PURE), `ProdCount` (the ×-count-Lens + the duality, 7 PURE); the tower /
`^`-rung and its commutativity boundary in `UnitHyper`, `HyperAssoc`, `HyperLadder`
(`count_hcube`, `swap_changes_dim`, `hyperop`). All ∅-axiom; each generated law's cone
verified free of the law it produces. The whole result is one citable theorem:
`Meta/Nat/GenerationCapstone.ordered_commutative_semiring_generated` (PURE) bundles the
eight generated laws (both monoids, both distributive bridges, the order,
`+`-monotonicity).

Signed counting (ℤ) is the dual axis, already 213-native: `Lens/Number/Int213/Raw.lean`
reads a `Raw` through `signedLens = ⟨1, −1, +⟩` (atom `a ↦ +1`, `b ↦ −1`), so a number
is the **difference** of its `a`-count and `b`-count, and **negation is the atom-swap**
`Raw.swap` (`value (neg r) = − value r`, `neg_neg = swap_swap`). The magnitude is the
count generated above; the sign is the Bool-style swap — the difference-Lens
(`theory/essays/analysis/integers_as_difference_lens.md`).

## Connection

- `theory/math/numbersystems/slot_arithmetic.md` — the slot tower (the rung structure
  this sits inside)
- `theory/essays/analysis/where_commutativity_is_born.md` — the seed essay (`+`-comm
  from unit-list append); this chapter generalizes it to the whole ordered semiring +
  the multiplicative dual
- `seed/AXIOM/06_lens_readings.md` §6.7 — "ℕ is what the count-Lens hands back"
