# The upper-fold pattern — proof as the same fold read at a finer resolution

A proof, in 213, is not an external argument brought to bear on an object.  It is the residue
pointing at itself; and when one pointing cannot close — a *wall* — the move is to read the **same**
pointing at a finer resolution.  The finer reading is again a fold: the `±` involution, the unit's
two faces, the same self-pointing one Lens-refinement down.  This recurrence is the *upper-fold
pattern*, and the worked instance is composite Markov uniqueness.

## 213-native answer

To prove `MarkovMaxUnique c` (Frobenius 1913: each Markov number is the maximum of one ordered
triple) you do not enumerate triples.  You fold.  The roots of `x² ≡ −1 (mod c)` carry the
involution `σ(u) = c − u` (`neg_root_is_root`); the window `0 < u < c/2` is its **transversal** —
one representative per `{u, c−u}` pair (`window_fold_transversal`, §20 of
`Real213/SternBrocotMarkov`).  Uniqueness becomes: *fold by `σ`, then the realised fold-point is
unique* (`WindowRealizedUnique`).  That is the whole shape; everything after is the same fold seen
closer.

## Derivation

Each wall, templatised, is again a fold (`theory/math/analysis/markov_uniqueness.md`, "The
upper-fold pattern"):

- **§21** — the wall "`σ` is just one symmetry" dissolves: the root set is a *torsor* under the
  unit-root group `SqrtUnity c = {e : e² ≡ 1}` (`sqrtUnity_acts_on_root`), and `σ` is its order-2
  element `c − 1 = −1` (`neg_one_sqrtUnity`, `neg_one_mul_is_neg`).  The involution was the group's
  distinguished generator all along.
- **§22** — the wall "why does `ω ≥ 2` explode" dissolves: the group is *multiplicative* across
  coprime factors (`sqrtUnity_lift`), so `SqrtUnity c` contains `∏ {±1 mod pᵢ}` — one `±` fold per
  prime.  The fold is a product of folds.  Made arithmetic: at `1325 = 25·53` the nontrivial
  unit-root `476` carries the realised root `507` to the phantom `182` (`476·507 ≡ 182`).
- **§23** — that product is *inhabited* beyond `±1` (`nontrivial_unit_root_exists`): by CRT,
  `e ≡ 1 mod m`, `e ≡ −1 mod n` gives `e ∉ {1, c−1}`.  Phantoms genuinely exist.
- **§24** — the group acts *freely* (`root_orbit_inj`): a root `u` is a unit with inverse `c − u`
  (`root_inverse`), so multiplication is cancellable.  The `2^ω` unit-roots give `2^ω` distinct
  roots; the window keeps `2^{ω−1}`.  The count is now *exact*.
- **§25–§27** — two distinct windowed roots are related by a nontrivial unit-root
  (`windowed_distinct_multiplier`), so `MarkovMaxUnique c` follows from a single hypothesis: *no
  nontrivial-unit-root image of a realised root is itself realised* (`markov_max_unique_of_orbit`).
  The tree residue is the distinguished realised suborbit (`tree_residue_realized_windowed`).

Seven sections, all ∅-axiom; the same `±` fold, seven resolutions down.

## Dual function

This is the classical Markov reduction with its packaging stripped: the literature's "the congruence
`x² ≡ −1` has `2^ω` roots and uniqueness needs the right one" is *exactly* the orbit count
`2^{ω−1}` plus the realisability hypothesis `H` — but 213 reads it sharper.  Root-counting is not the
open problem (it is closed: free action fixes the count); the open content is *realisability* of one
`±`-suborbit, an `∃!`-statement, not a counting one.  The classical "open: count the roots" was
already a fold the framework can see through.

## Cross-frame connections

The fold the window transverses is the fold the repo reads everywhere as the unit's two faces:
the `Δ = tr² − 4` sign splitting hyperbolic `φ` from elliptic `π` (`HyperbolicEllipticTrace`), `0`
and `∞` as one reciprocal hole (`ZeroInfinityHole`), the `±`/Cassini sign as the fold's non-value
(`DetSpectrumPoles`).  And `±` itself is the readout of the difference-Lens
(`theory/essays/integers_as_difference_lens.md`).  `WindowRealizedUnique` is "the fold's realised
non-value is unique" — the Markov face of the same object.

## Why this is forced, not heuristic

"Templatise the wall; the template is again a fold" is not a lucky regularity — it is a consequence
of no-exterior (`seed/AXIOM/05_no_exterior.md` §5.1, §8.1).  An obstruction cannot be *external*:
there is no outside to locate it in.  So every wall is internal self-reference, and internal
self-reference correctly abstracted *is* a fold — the residue pointing at itself
(`theory/essays/the_form_of_the_residue.md`).  The recursion does not bottom out into a non-fold
base case because no view surjects onto the residue (`object1_not_surjective`,
`theory/math/completeness_without_completeness.md`): each template is a facet, the residue is outside
every facet's image, so refinement *converges* on the residue without ever *reaching* a final
non-fold.  Proof closes by folding; it does not terminate at an atom.

## Open frontier

The fold tower closes everything *around* `H` — count, group, free action, existence, *which*
suborbit realises (the tree residue) — and the reduction is now an **equivalence**, not a sufficiency:
`MarkovMaxUnique c ↔ WindowRealizedUnique c ↔ OrbitRealizabilityH c` is `∅`-axiom
(`markovMaxUnique_iff_orbitRealizabilityH`).  But read that honestly: what is closed is *that the three
are equivalent*, not their truth value — the chain's last link is the open conjecture.  The output is
*"Frobenius restated, exactly, in `∅`-axiom orbit/window form"*, not progress toward its proof; the
pattern reaches `H` and names it precisely, it does not dissolve it.

And the difficulty does not sit where it first looks.  `slope_path_inj` is non-constructive, so a
residue does not hand back a triple with the present objects — but that is *labor* (extract a
`(u,c) → path` recovery function; injectivity is already `∅`-axiom, so its inverse is well-defined),
not a barrier.  Even a recovery function would only reduce `H` to a decidable check ("does the
recovered node have max `= c`?") — bypassing the `decide` wall — and recovery (find the triple at `c`,
unique if it exists) is *not* `H` (does a triple at `c` exist).  `H`'s real weight is the cross-`c`
**passing pattern**: which `ℤ` lift survives the full Vieta descent.  That pattern is the conjecture
itself — classically, the monotone-slope characterisation (stable norm / Christoffel words).  Honest
closure is "the reduction is exact and the kernel is named," not "the conjecture is nearly resolved."
