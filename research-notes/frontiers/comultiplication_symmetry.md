# Comultiplication symmetry — comm/assoc as shadows of one cut symmetry

**The slot-programme doctrine, made a theorem ladder.**  The 213 co-operation `splits`
(`CoAppend213`) cuts one thing into two — the `+`-inverse question ("which `(i,j)` glue to
`n`?", `mem_splits_iff`).  Its ℕ shadow `natSplits n = {(i,j) : i+j=n}` is a **comultiplication**.
The doctrine: *commutativity and associativity of an operation are shadows of a swap/reindex
symmetry of the underlying comultiplication.*  This is now closed at three rungs:

| rung | operation | symmetry | Lean |
|---|---|---|---|
| `+` (lists) | `append` | reverse/swap of the glue | `UnitList.append_comm` |
| `×` (grid) | `mul` | transpose of the unit grid | `UnitGrid.mul_comm_from_grid` |
| `conv` (sequences) | Cauchy product `Σ_{i+j=n} f_i g_j` | **cut-reversal** (comm) + **cut-coassociativity** (assoc) | `Convolution213.conv_comm`, `conv_assoc` |

**`conv_assoc` (the new brick, PURE).**  `conv (conv f g) h = conv f (conv g h)` — the triple
split reindexes because cutting `n` into three pieces two ways enumerates the same
`{(i,j,k) : i+j+k=n}`.  This is the **coassociativity** `(Δ⊗I)Δ = (I⊗Δ)Δ` of the cut
comultiplication, dual to Cauchy-product associativity.  Proven in the file's own end-peel
style (no full sum-permutation lemma): peel the outer-left cut on both sides; the left nest's
shifted head `shiftL(conv f g) = f₀·(shiftL g) + conv (shiftL f) g` splits by bilinearity
(`conv_add_left`) and scalar linearity (`conv_smul_left`, new), the inner block folds by
induction, the heads agree by `mul_assoc`.  Helpers `sumMap_congr`/`sumMap_smul`/`conv_smul_left`/
`conv_congr_left` keep it `funext`-free.

## Honest novelty (adversarial web check)

- **Conceded classical.**  The fact is the **divided-power / cofree-coalgebra** comultiplication
  `Δ(Z_n)=Σ_{i+j=n}Z_i⊗Z_j` and its coassociativity = Cauchy-product associativity (Hopf-algebra
  combinatorics; Grinberg–Reiner; Wikipedia *Cauchy product*, *Coalgebra*).  No new theorem of
  algebra.
- **Genuinely unwritten** (the residue): the *explicit constructive ℕ comultiplication*
  `natSplits`/`splits` with coassociativity proven (i) at a **strictly empty axiom set** (no
  `propext`/`Quot.sound`/`Classical`/`funext` — every `Finset.sum`-based proof carries `propext`),
  and (ii) framed as the **sequence-scale rung of the slot-programme doctrine** "comm+assoc are
  shadows of a comultiplication swap symmetry", tying `splits` (the `+`-inverse comultiplication)
  to `conv` (the generating-function product) by one shared mechanism, alongside `append_comm` and
  `mul_comm_from_grid`.  The ladder `append(+) / grid(×) / splits(conv)` is now a theorem, not a
  picture.  This is the "algebra OF the objects and their framing" the finite-signature program
  flags as the live edge — a doctrine-completing cross-relation, not new analysis.

## Open continuation

- **`conv` as a commutative monoid / the unit `δ₀`**: `conv f δ = f` for the delta sequence
  `δ = [1,0,0,…]`, completing `(Nat→Nat, conv, δ₀, addSeq)` as a commutative semiring — the
  generating-function ring, ∅-axiom.
- **right bilinearity** `conv_add_right` (mirror of `conv_add_left`) by `conv_comm`.
- **the comultiplication coassociativity stated directly** on `natSplits` (the `T:ℕ→ℕ→ℕ→ℕ`
  three-cut form), with `conv_assoc` as the `T = f·g·h` corollary — making the doctrine
  statement carrier-level, not conv-level.
